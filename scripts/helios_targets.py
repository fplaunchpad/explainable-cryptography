"""Computational target inventories, derived from explicit Lean import roots."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'ExplainableCrypto.Helios.Computational.'
CASE_STUDY = 'ExplainableCrypto.Helios.Computational'
FULL = 'ExplainableCrypto.Helios.Execution'


def module_path(name):
    return ROOT / (name.replace('.', '/') + '.lean')


def imports(name):
    # Current project imports have one module per line. Strip comments first.
    text = re.sub(r'/\-.*?\-/', '', module_path(name).read_text(), flags=re.S)
    return re.findall(r'^import\s+(\S+)', text, re.M)


def closure(roots):
    pending, seen = list(roots), set()
    while pending:
        name = pending.pop()
        if name in seen or not module_path(name).is_file():
            continue
        seen.add(name)
        pending.extend(imports(name))
    return seen


def computational(names):
    return {n for n in names if n.startswith(PREFIX)}


def inventory():
    all_modules = {PREFIX + p.stem for p in (ROOT / 'ExplainableCrypto/Helios/Computational').glob('*.lean')}
    roots = imports(CASE_STUDY)
    retained = computational(closure(roots))
    full = computational(closure([FULL]))
    if full != all_modules:
        raise RuntimeError(f'Full target missing {sorted(all_modules - full)}; extra {sorted(full - all_modules)}')
    return roots, retained, all_modules
