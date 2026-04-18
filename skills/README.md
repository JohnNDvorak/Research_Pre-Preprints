# Codex Skills

This directory contains shareable Codex skills.

## Self-Drive Research Loop

The packaged skill is:

```text
skills/self-drive-research-loop/
```

To install it into Codex from this repository:

```bash
mkdir -p ~/.codex/skills
cp -R skills/self-drive-research-loop ~/.codex/skills/
```

Or run the installer from the repository root:

```bash
./install_self_drive_skill.sh
```

After installation, start a Codex session and ask for:

```text
Use $self-drive-research-loop to set up a research loop for this problem.
```

The skill is intentionally lightweight. It provides the workflow and ledger discipline; it does not certify mathematical proofs.

The workflow review and install note live with the skill:

```text
skills/self-drive-research-loop/docs/self_drive_skill_review.md
skills/self-drive-research-loop/docs/self_drive_skill_review.pdf
```
