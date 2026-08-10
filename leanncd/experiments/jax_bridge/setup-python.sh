#!/usr/bin/env bash

set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ENV_DIR="$HERE/.cache/python"
REQUIREMENTS="$HERE/requirements-cpu.txt"

if [[ -x "$ENV_DIR/bin/python" ]]; then
  echo "Using existing environment at $ENV_DIR"
elif [[ -n "${PYTHON:-}" ]]; then
  "$PYTHON" -m venv "$ENV_DIR"
else
  for candidate in python3.13 python3.12 python3.11; do
    if command -v "$candidate" >/dev/null 2>&1; then
      if "$candidate" -m venv "$ENV_DIR"; then
        break
      fi
      rm -rf "$ENV_DIR"
    fi
  done

  if [[ ! -x "$ENV_DIR/bin/python" && -x "$HOME/miniconda3/bin/python" ]]; then
    if ! "$HOME/miniconda3/bin/python" -m venv "$ENV_DIR"; then
      rm -rf "$ENV_DIR"
    fi
  fi

  if [[ ! -x "$ENV_DIR/bin/python" ]]; then
    if command -v conda >/dev/null 2>&1; then
      conda create --yes --prefix "$ENV_DIR" python=3.12 pip
    else
      echo "Python 3.11+ is required and no supported interpreter or conda was found." >&2
      exit 1
    fi
  fi
fi

"$ENV_DIR/bin/python" -m pip install -r "$REQUIREMENTS"
"$ENV_DIR/bin/python" -c \
  'import jax; print(f"Installed JAX {jax.__version__}; devices: {jax.devices()}")'
