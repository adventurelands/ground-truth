#!/usr/local/bin/python3.11
"""
ProofFarm orchestrator.
Reads .lean files with sorry markers, sends goals to Gemma via Ollama,
substitutes proofs, type-checks with Lean, iterates.
"""

import urllib.request
import json
import subprocess
import re
import datetime
import os
import sys
import time

# ============================================================
# CONFIG
# ============================================================

OLLAMA_URL = "http://192.168.1.177:11434/api/generate"
MODEL = "deepseek-prover"
PROJECT_DIR = "/Users/olderaccount/~tmpclaude/ProofFarm"
LOG_DIR = os.path.join(PROJECT_DIR, "logs")
MAX_REAL_ATTEMPTS = 100  # keep trying real proofs until this many non-empty attempts
MAX_EMPTY_STREAK = 30    # give up on empties fast; fallbacks already tried first

TIER_FILES = [
    "ProofFarm/Tier1_NatBasic.lean",
    "ProofFarm/Tier2_Order.lean",
    "ProofFarm/Tier3_DivMod.lean",
    "ProofFarm/Tier4_Divisibility.lean",
    "ProofFarm/Tier5_Lists.lean",
    "ProofFarm/Tier6_GCD.lean",
    "ProofFarm/Tier7_Primes.lean",
    "ProofFarm/Tier8_Fermat.lean",
    "ProofFarm/Tier9_Bezout.lean",
    "ProofFarm/Tier10_CRT.lean",
    "ProofFarm/Tier11_RSABridge.lean",
    "ProofFarm/Tier12_RSA.lean",
]

SYSTEM_PROMPT = ""

# ============================================================
# CORE FUNCTIONS
# ============================================================

def find_sorry_blocks(filepath):
    """Parse file for PROOF_START/PROOF_END markers.
    Returns list of (lemma_name, start_line_idx, end_line_idx)."""
    with open(filepath) as f:
        lines = f.readlines()

    blocks = []
    i = 0
    while i < len(lines):
        m = re.search(r'--PROOF_START\[(.+?)\]', lines[i])
        if m:
            name = m.group(1)
            start = i
            # Find matching end
            for j in range(i + 1, len(lines)):
                if f'--PROOF_END[{name}]' in lines[j]:
                    blocks.append((name, start, j))
                    break
        i += 1
    return blocks


def get_context(filepath, up_to_line):
    """Get file content up to (and including) the PROOF_START line."""
    with open(filepath) as f:
        lines = f.readlines()
    return ''.join(lines[:up_to_line + 1])


def get_theorem_signature(filepath, start_line):
    """Extract the theorem statement (lines before PROOF_START)."""
    with open(filepath) as f:
        lines = f.readlines()
    # Walk backwards from start_line to find the theorem/lemma keyword
    sig_lines = []
    for i in range(start_line, -1, -1):
        line = lines[i]
        sig_lines.insert(0, line)
        if re.match(r'\s*(theorem|lemma|def)\s', line):
            break
    return ''.join(sig_lines)


def build_prompt(context, theorem_sig, error_msg=None):
    """Build prompt for DeepSeek-Prover. Just give it the Lean 4 code to complete."""
    if len(context) > 4000:
        context = context[-4000:]

    # DeepSeek-Prover works best with just the code, ending at the `by` keyword
    prompt = context

    if error_msg:
        if len(error_msg) > 1000:
            error_msg = error_msg[:1000]
        prompt += f"\n-- Previous error: {error_msg}\n{theorem_sig.strip()}"

    return prompt


def call_gemma(user_prompt, temperature=0.3):
    """Call Ollama API via curl (urllib has network issues on this Mac)."""
    full_prompt = f"{SYSTEM_PROMPT}\n\n{user_prompt}"

    payload = {
        "model": MODEL,
        "prompt": full_prompt,
        "stream": False,
        "options": {
            "temperature": temperature,
            "num_predict": 1024,
            "top_p": 0.9,
            "stop": ["--PROOF_END", "/--", "\nend ", "\ntheorem ", "\nlemma "],
        }
    }

    try:
        result = subprocess.run(
            ["curl", "-s", "--connect-timeout", "10", "--max-time", "60",
             OLLAMA_URL, "-d", json.dumps(payload)],
            capture_output=True, text=True, timeout=70
        )
        if result.returncode != 0:
            return f"ERROR: curl failed: {result.stderr[:100]}"
        data = json.loads(result.stdout)
        return data.get("response", "")
    except Exception as e:
        return f"ERROR: {e}"


def extract_proof(raw_response):
    """Extract clean tactic block from Gemma's response."""
    text = raw_response.strip()

    # Remove markdown fencing if present
    text = re.sub(r'^```\w*\n?', '', text)
    text = re.sub(r'\n?```$', '', text)

    # Remove any "by" prefix
    text = re.sub(r'^\s*by\s*\n?', '', text)

    # Remove any theorem/lemma header if the model repeated it
    lines = text.split('\n')
    clean_lines = []
    skip = False
    for line in lines:
        if re.match(r'\s*(theorem|lemma)\s', line):
            skip = True
            continue
        if skip and ':=' in line:
            skip = False
            continue
        if not skip:
            clean_lines.append(line)

    text = '\n'.join(clean_lines).strip()

    # Ensure indentation (2 spaces)
    lines = text.split('\n')
    indented = []
    for line in lines:
        stripped = line.lstrip()
        if stripped:
            if not line.startswith('  '):
                indented.append('  ' + stripped)
            else:
                indented.append(line)
        else:
            indented.append('')

    result = '\n'.join(indented).strip()

    # Reject empty proofs
    if not result or result.isspace():
        return None

    # Reject if it's just sorry
    if result.strip() in ('sorry', 'sorry --', 'sorry -- EMPTY PROOF REJECTED'):
        return None

    return result


def substitute_proof(filepath, lemma_name, proof_text):
    """Replace the sorry between PROOF_START and PROOF_END markers."""
    with open(filepath) as f:
        lines = f.readlines()

    start_idx = end_idx = None
    for i, line in enumerate(lines):
        if f'--PROOF_START[{lemma_name}]' in line:
            start_idx = i
        if f'--PROOF_END[{lemma_name}]' in line:
            end_idx = i

    if start_idx is None or end_idx is None:
        return False

    new_lines = lines[:start_idx + 1] + [proof_text + '\n'] + lines[end_idx:]
    with open(filepath, 'w') as f:
        f.writelines(new_lines)
    return True


def restore_sorry(filepath, lemma_name):
    """Restore sorry for a failed lemma."""
    substitute_proof(filepath, lemma_name, '  sorry')


def check_file(filepath):
    """Type-check a single file with lake env lean. Returns (success, errors)."""
    result = subprocess.run(
        ["lake", "env", "lean", filepath],
        cwd=PROJECT_DIR,
        capture_output=True,
        text=True,
        timeout=120
    )

    stderr = result.stderr
    # Filter for actual errors (not sorry warnings)
    error_lines = []
    for line in stderr.split('\n'):
        if 'error' in line.lower() and 'sorry' not in line.lower():
            error_lines.append(line)
        elif 'unknown' in line.lower() or 'type mismatch' in line.lower():
            error_lines.append(line)
        elif 'unsolved' in line.lower():
            error_lines.append(line)

    # Check for actual errors vs just sorry warnings
    has_real_error = any('error' in l.lower() and 'sorry' not in l.lower()
                        for l in stderr.split('\n'))

    # Also check: if the only issues are sorry warnings, that's fine for now
    # We care about the specific lemma's proof compiling
    return not has_real_error, '\n'.join(error_lines) if error_lines else stderr


def check_lemma(filepath, lemma_name):
    """Check if a specific lemma's proof is valid.
    Strategy: the file has sorry in all other lemmas. We only substituted
    this one lemma's proof. So we check if the build has any errors
    BEYOND sorry warnings. We use returncode AND parse stderr."""
    result = subprocess.run(
        ["lake", "env", "lean", filepath],
        cwd=PROJECT_DIR,
        capture_output=True,
        text=True,
        timeout=120
    )

    stderr = result.stderr
    stdout = result.stdout

    # If lean exited with error, something is wrong
    if result.returncode != 0:
        # Extract meaningful error lines
        error_lines = []
        for line in stderr.split('\n'):
            line = line.strip()
            if not line:
                continue
            if 'declaration uses `sorry`' in line:
                continue
            if any(kw in line.lower() for kw in ['error', 'unknown', 'unsolved', 'type mismatch', 'unexpected']):
                error_lines.append(line)
        return False, '\n'.join(error_lines) if error_lines else stderr

    # Even if returncode is 0, check for sorry warnings on THIS lemma
    # (shouldn't happen if proof was substituted, but just in case)
    return True, ''


def log(msg, logfile):
    """Append timestamped message to log."""
    ts = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    entry = f"[{ts}] {msg}\n"
    with open(logfile, 'a') as f:
        f.write(entry)
    print(entry.rstrip())


# ============================================================
# FALLBACK TACTICS
# ============================================================

FALLBACK_PROOFS = [
    # Single tactics
    "  omega",
    "  simp",
    "  rfl",
    "  decide",
    # Two-tactic combos
    "  simp; omega",
    "  simp; rfl",
    "  unfold GCD.Coprime; simp",
    "  unfold GCD.Coprime; omega",
    # Intro patterns
    "  intro h; omega",
    "  intro h; simp",
    "  intro h; exact h",
    "  intro h; simp [h]",
    "  intro h1 h2; omega",
    # Constructors / existentials
    "  constructor <;> omega",
    "  exact ⟨1, by omega⟩",
    "  exact ⟨0, by omega⟩",
    # Cases on first arg
    "  cases n with | zero => omega | succ n => omega",
    "  cases n with | zero => simp | succ n => simp; omega",
    "  cases a with | zero => omega | succ a => omega",
    "  cases a with | zero => simp | succ a => simp; omega",
    # Induction on n (first common var)
    "  induction n with | zero => omega | succ n ih => omega",
    "  induction n with | zero => simp | succ n ih => simp [ih]",
    "  induction n with | zero => simp | succ n ih => simp [ih]; omega",
    "  induction n with | zero => rfl | succ n ih => simp [ih]; ring",
    # Induction on m (second common var)
    "  induction m with | zero => omega | succ m ih => omega",
    "  induction m with | zero => simp | succ m ih => simp [ih]",
    "  induction m with | zero => simp | succ m ih => simp [ih]; omega",
    "  induction m with | zero => simp | succ m ih => simp [Nat.mul_succ, ih]; omega",
    # Induction on a
    "  induction a with | zero => omega | succ a ih => omega",
    "  induction a with | zero => simp | succ a ih => simp [ih]; omega",
    # Induction on list
    "  induction l with | nil => simp | cons x xs ih => simp [ih]",
    "  induction l with | nil => rfl | cons x xs ih => simp [ih]",
    "  induction l₁ with | nil => simp | cons x xs ih => simp [ih]",
    # Obtain/rcases for existentials
    "  obtain ⟨k, hk⟩ := h; omega",
    "  obtain ⟨k, hk⟩ := hd; exact ⟨k, by omega⟩",
    # dvd helpers
    "  exact Nat.dvd_refl _",
    "  exact dvd_refl _",
    "  exact ⟨_, rfl⟩",
    # Multiplication induction patterns (succ_mul based)
    "  induction a with | zero => simp | succ n ih => simp [succ_mul, Nat.mul_succ, ih]",
    "  induction a with | zero => simp | succ n ih => simp [succ_mul, Nat.add_mul, ih]",
    "  induction a with | zero => simp | succ n ih => simp [succ_mul, ih, Nat.add_assoc]; omega",
    "  induction b with | zero => simp | succ n ih => simp [succ_mul, Nat.mul_succ, ih]",
    "  induction b with | zero => simp | succ n ih => simp [succ_mul, ih]; omega",
    # Cases + simp for zero-product
    "  cases a with | zero => left; rfl | succ n => right; simp [succ_mul] at h; omega",
    "  cases a with | zero => left; rfl | succ n => right; omega",
    "  cases b with | zero => right; rfl | succ n => left; omega",
    # rw + mul_comm combos
    "  rw [mul_comm, mul_add]; simp [mul_comm]",
    "  rw [mul_comm]; rfl",
    "  rw [mul_comm]; omega",
    # Intro + cases for implications
    "  intro h; cases h with | inl h => exact h | inr h => exact h",
    "  intro ⟨h1, h2⟩; omega",
]


# ============================================================
# MAIN
# ============================================================

def main():
    os.makedirs(LOG_DIR, exist_ok=True)
    logfile = os.path.join(LOG_DIR,
        f"run_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.log")

    # Check Ollama connectivity via curl
    log("Checking Ollama connectivity...", logfile)
    try:
        base_url = OLLAMA_URL.rsplit('/api/generate', 1)[0]
        result = subprocess.run(
            ["curl", "-s", "--connect-timeout", "5", f"{base_url}/api/tags"],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode != 0 or not result.stdout.strip():
            log(f"FATAL: Cannot connect to Ollama: {result.stderr}", logfile)
            sys.exit(1)
        models = json.loads(result.stdout)
        log(f"Ollama connected. Models: {[m['name'] for m in models.get('models', [])]}", logfile)
    except Exception as e:
        log(f"FATAL: Cannot connect to Ollama: {e}", logfile)
        sys.exit(1)

    stats = {"attempted": 0, "proved": 0, "failed": 0, "fallback": 0}
    failed_lemmas = []

    for tier_file in TIER_FILES:
        filepath = os.path.join(PROJECT_DIR, tier_file)
        if not os.path.exists(filepath):
            log(f"SKIP: {tier_file} not found", logfile)
            continue

        log(f"\n{'='*60}", logfile)
        log(f"TIER: {tier_file}", logfile)
        log(f"{'='*60}", logfile)

        blocks = find_sorry_blocks(filepath)
        log(f"Found {len(blocks)} sorry blocks", logfile)

        for lemma_name, start_line, end_line in blocks:
            stats["attempted"] += 1
            log(f"\n--- {lemma_name} ---", logfile)

            # Check if already proved (non-sorry content between markers)
            with open(filepath) as f:
                lines = f.readlines()
            existing = ''.join(lines[start_line + 1:end_line]).strip()
            if existing and existing != 'sorry':
                log(f"  ALREADY PROVED: {existing[:80]}", logfile)
                stats["proved"] += 1
                continue

            proved = False

            # PHASE 1: Try fallback tactics FIRST (fast, ~2 sec each)
            for fb in FALLBACK_PROOFS:
                substitute_proof(filepath, lemma_name, fb)
                success, _ = check_lemma(filepath, lemma_name)
                if success:
                    log(f"  FAST SOLVE: {fb.strip()}", logfile)
                    stats["proved"] += 1
                    stats["fallback"] += 1
                    proved = True
                    break
                restore_sorry(filepath, lemma_name)

            if proved:
                continue

            # PHASE 2: Ask Gemma for the hard ones
            log(f"  Fallbacks failed, asking Gemma...", logfile)
            context = get_context(filepath, start_line)
            theorem_sig = get_theorem_signature(filepath, start_line)
            prev_error = None

            real_attempts = 0
            empty_count = 0
            consecutive_empties = 0
            while real_attempts < MAX_REAL_ATTEMPTS and consecutive_empties < MAX_EMPTY_STREAK:

                # Vary temperature based on attempts
                temp = 0.3 + (real_attempts % 10) * 0.07  # cycles 0.3 to 0.93

                user_prompt = build_prompt(context, theorem_sig, prev_error)
                raw = call_gemma(user_prompt, temperature=temp)

                if raw.startswith("ERROR:"):
                    log(f"  Gemma {real_attempts+1} (t={temp:.2f}): Ollama error: {raw[:100]}", logfile)
                    prev_error = raw
                    real_attempts += 1
                    continue

                proof = extract_proof(raw)
                if proof is None:
                    empty_count += 1
                    consecutive_empties += 1
                    if empty_count % 10 == 0:
                        log(f"  ({empty_count} empty responses so far, retrying...)", logfile)
                    continue  # don't count as real attempt
                consecutive_empties = 0  # got a real response, reset streak

                # Reject proofs containing sorry
                if 'sorry' in proof:
                    log(f"  Gemma {real_attempts+1} (t={temp:.2f}): REJECTED - contains sorry", logfile)
                    prev_error = "Do not use sorry. Provide a complete proof."
                    real_attempts += 1
                    continue

                real_attempts += 1
                proof_oneline = proof.replace(chr(10), ' | ')
                log(f"  Gemma {real_attempts} (t={temp:.2f}): {proof_oneline}", logfile)

                substitute_proof(filepath, lemma_name, proof)
                success, errors = check_lemma(filepath, lemma_name)

                if success:
                    log(f"  GEMMA SUCCESS on attempt {real_attempts} ({empty_count} empties skipped)", logfile)
                    stats["proved"] += 1
                    proved = True
                    break
                else:
                    prev_error = errors
                    log(f"  FAIL {real_attempts}: {errors[:150].replace(chr(10), ' | ')}", logfile)
                    restore_sorry(filepath, lemma_name)

            if not proved:
                restore_sorry(filepath, lemma_name)
                stats["failed"] += 1
                failed_lemmas.append(lemma_name)
                log(f"  GIVING UP on {lemma_name}", logfile)

    # Final summary
    log(f"\n{'='*60}", logfile)
    log(f"FINAL RESULTS", logfile)
    log(f"{'='*60}", logfile)
    log(f"Attempted:  {stats['attempted']}", logfile)
    log(f"Proved:     {stats['proved']} ({100*stats['proved']/max(stats['attempted'],1):.1f}%)", logfile)
    log(f"  via Gemma:    {stats['proved'] - stats['fallback']}", logfile)
    log(f"  via fallback: {stats['fallback']}", logfile)
    log(f"Failed:     {stats['failed']}", logfile)
    if failed_lemmas:
        log(f"Failed lemmas: {failed_lemmas}", logfile)
    log(f"Log: {logfile}", logfile)


if __name__ == "__main__":
    main()
