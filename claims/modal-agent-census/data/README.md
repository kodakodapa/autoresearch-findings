# Datasets

Data files read by the checks in `../checks/`. Each check pins the sha256 of the file it
reads and opens it by the absolute path shown below.

- `data/census/census9.json` (2.0 MB): read by the checks as
  `/run/agents/r1/census/census9.json`; sha256 `82b872829655bbcc898e1e03213ff3f0f44da86a720b2fa9c9ad7c8992d6c6e2`
- `data/census/census11_M.zlib` (11.9 MB): read by the checks as
  `/run/agents/r1/census/census11_M.zlib`; sha256 `4cf7d9895fc0267f9e2473ae8c4d5de78c6e97d09d31394ddd0ac342c3dab31b`
- `data/census/census11_agents.json` (0.5 MB): read by the checks as
  `/run/agents/r1/census/census11_agents.json`; sha256 `04a4a117183b345ba543b77b5a5841cbf064f068d960eba5a270da5e0255bb7a`

To re-run a check locally, make each file available at the path it reads, by copying it
there or creating a symlink (for example `ln -s $PWD/census/x.json /run/agents/r1/census/
x.json`), then run `python -I checks/<script>.py`.
