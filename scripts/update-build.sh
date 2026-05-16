#!/usr/bin/env bash
set -euo pipefail

# Deve ser rodado na raiz do projeto Lake.

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "Erro: rode este script na raiz do projeto Lake."
  exit 1
fi

repo_root="$PWD"
if git rev-parse --show-toplevel >/dev/null 2>&1; then
  repo_root="$(git rev-parse --show-toplevel)"
fi
repo_name="$(basename "$repo_root")"

# Fallback para o nome do repositório quando não for possível detectar o pacote.
pkg_name="$repo_name"
if [ -f lakefile.toml ]; then
  detected_pkg="$(sed -n 's/^name = "\(.*\)"/\1/p' lakefile.toml | head -n1)"
  if [ -n "$detected_pkg" ]; then
    pkg_name="$detected_pkg"
  fi
fi

echo "==> Repositório: $repo_name"
echo "==> Pacote Lean: $pkg_name"

echo "==> Rodando lake update..."
lake update

echo "==> Baixando cache da mathlib..."
lake exe cache get

echo "==> Compilando..."
lake build

echo "==> Rodando leanchecker..."
lake env leanchecker "$pkg_name"

echo "==> Pronto."
