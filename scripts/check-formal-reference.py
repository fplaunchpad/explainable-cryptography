#!/usr/bin/env python3
"""Check printed Lean anchors, local links, typed displays and reported axioms.

This checks evidence correspondence, not mathematical prose equivalence.
Run from any directory; the main library must already have been built.
"""
from pathlib import Path
import re
import argparse
from helios_targets import closure, computational, inventory
import subprocess
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs/formal-reference/main.tex"
OUT = ROOT / "tmp/formal-reference/reference"
DOCUMENTS = {"reference": ("main.tex", "StatementChecks.lean", 8),
             "catalogue": ("catalogue.tex", "CatalogueStatementChecks.lean", 4)}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def source_snippets():
    source = (ROOT / "ExplainableCrypto/Helios/Computational/ElectionSecurityFamily.lean").read_text()
    family = source[source.index("structure Family ("):source.index("/-- Natural-coefficient")].rstrip() + "\n"
    start = source.index("theorem ballot_secrecy\n")
    theorem = source[start:source.index(" := by", start)] + "\n"
    start = source.index("variable {q :")
    context = source[start:source.index("\n\n", start)] + "\n"
    return {"Family.lean": family, "BallotSecrecy.lean": theorem, "Context.lean": context}


def validate_snippets(tex, directory=None):
    directory = directory or DOC.parent / "statements"
    for name, expected in source_snippets().items():
        path = directory / name
        if not path.exists() or path.read_text() != expected:
            raise ValueError(f"Stale or missing verbatim statement: {name}")
        if "{statements/" + name + "}" not in tex:
            raise ValueError(f"Verbatim statement not included: {name}")


def anchors(tex, macro="anchor", source_root=None, required=True):
    # Ignore macro definitions and comments; all actual invocations are literal.
    text = tex.split(r"\begin{document}", 1)[1]
    source_root = source_root or ROOT / "ExplainableCrypto/Helios"
    entries = re.findall(r"\\" + macro + r"\{([^{}]+)\}\s*\{([^{}]+)\}", text)
    if (required and not entries) or len(entries) != text.count("\\" + macro + "{"):
        raise ValueError("Missing or malformed Lean anchor")
    for module, name in entries:
        if not re.fullmatch(r"[A-Za-z0-9_/]+", module):
            raise ValueError(f"Invalid module: {module}")
        if not (source_root / (module + ".lean")).is_file():
            raise ValueError(f"Missing source: {module}")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
            raise ValueError(f"Invalid declaration: {name}")
    return list(dict.fromkeys(entries))


def validate_links(tex):
    count = 0
    for target in re.findall(r"\\href\{([^{}]+)\}", tex):
        if "#1" in target or target.startswith(("http://", "https://")):
            continue
        path = unquote(target.replace(r"\%", "%").split("#")[0])
        if not (DOC.parent / path).exists():
            raise ValueError(f"Missing local link: {target}")
        count += 1
    labels = re.findall(r"\\label\{([^{}]+)\}", tex)
    if len(labels) != len(set(labels)):
        raise ValueError("Duplicate LaTeX label")
    refs = set(re.findall(r"\\(?:ref|pageref)\{([^{}]+)\}", tex))
    if refs - set(labels):
        raise ValueError(f"Unresolved LaTeX references: {refs - set(labels)}")
    cites = set(re.findall(r"\\cite\{([^{}]+)\}", tex))
    bib = set(re.findall(r"\\bibitem\{([^{}]+)\}", tex))
    if cites - bib:
        raise ValueError(f"Unresolved bibliography: {cites - bib}")
    return count


def audit_log(log, expected):
    if re.search(r"sorryAx|\b(?:error|warning):", log):
        raise ValueError("Lean log contains a warning, error or sorryAx")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", log)
    if len(reports) + len(empty) != expected:
        raise ValueError("Missing or duplicate axiom reports")
    for name, report in reports:
        unexpected = set(re.findall(r"[\w.]+", report)) - ALLOWED
        if unexpected:
            raise ValueError(f"Unexpected axioms for {name}: {unexpected}")


def run_lean(source, log_name, expected, cwd=ROOT):
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=cwd,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / log_name).write_text(result.stdout)
    if result.returncode:
        raise ValueError(f"Lean failed; see {(OUT / log_name).relative_to(ROOT)}")
    audit_log(result.stdout, expected)


def validate_scope(modules, statement_source):
    """Every imported project dependency in the concise reference is retained."""
    imports = re.findall(r"^import\s+(\S+)", statement_source, re.M)
    _, retained, _ = inventory()
    deferred = computational(closure([*modules, *imports])) - retained
    if deferred:
        raise ValueError(f"Reference reaches deferred execution modules: {sorted(deferred)}")


def validate_language(tex, document):
    # Statements and source citations retain exact identifiers. Inspect prose only.
    prose = tex.split(r"\begin{document}", 1)[1]
    prose = re.sub(r"\\begin\{(?:Verbatim|lstlisting)\}.*?\\end\{(?:Verbatim|lstlisting)\}", "", prose, flags=re.S)
    prose = re.sub(r"\\(?:companchor|anchor)\{[^{}]+\}\s*\{[^{}]+\}", "", prose)
    prose = re.sub(r"(?m)(?<!\\)%.*$", "", prose)
    prose = " ".join(prose.split())
    if document == "reference":
        pattern = (r"\b(?:milestones?|checkpoints?|falsifiers?|positive controls?|"
                   r"negative controls?)\b|integrated/audited|package complete|"
                   r"\b[BC]\d{1,2}\b|\b3\s*/\s*3\b")
    else:
        pattern = (r"\b(?:remains?|still)\s+(?:open|partial|active|pending|unresolved)\b|"
                   r"\bintended endpoint\b|\bno checkpoint closes\b|\bnot yet (?:proved|closed|complete)\b")
    match = re.search(pattern, prose, re.I)
    if match:
        raise ValueError(f"{document} contains obsolete status or internal vocabulary: {match.group()}")


def main():
    global DOC, OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--document", choices=DOCUMENTS, default="reference")
    args = parser.parse_args()
    filename, statement_file, statement_count = DOCUMENTS[args.document]
    DOC = ROOT / "docs/formal-reference" / filename
    OUT = ROOT / "tmp/formal-reference" / args.document
    OUT.mkdir(parents=True, exist_ok=True)
    tex = DOC.read_text()
    if args.document == "reference":
        validate_snippets(tex)
    validate_language(tex, args.document)
    entries = anchors(tex, required=args.document == "reference")
    computational_entries = anchors(tex, "companchor", ROOT / "ExplainableCrypto/Helios/Computational")
    statements = DOC.parent / statement_file
    imports = ["ExplainableCrypto.Helios." + m.replace("/", ".") for m, _ in entries]
    imports += ["ExplainableCrypto.Helios.Computational." + m.replace("/", ".")
                for m, _ in computational_entries]
    if args.document == "reference":
        validate_scope(imports, statements.read_text())
    links = validate_links(tex)
    counts = []
    for citations, prefix, namespace, opening, stem in [
        (entries, "ExplainableCrypto.Helios.", "ExplainableCrypto.Helios.Symbolic",
         "open Historical Historical.General Historical.General.Source\n", "citations"),
        (computational_entries, "ExplainableCrypto.Helios.Computational.",
         "ExplainableCrypto.Helios.Computational", "", "computational-citations")]:
        modules = sorted({m for m, _ in citations})
        names = sorted({n for _, n in citations})
        counts.append(len(names))
        if not names:
            continue
        source = "\n".join("import " + prefix + m.replace("/", ".") for m in modules)
        source += "\nnamespace " + namespace + "\n" + opening
        source += "\n".join(f"#check {n}\n#print axioms {n}" for n in names)
        source += "\nend " + namespace + "\n"
        generated = OUT / (stem.replace("-", "_") + ".lean")
        generated.write_text(source)
        run_lean(generated, stem + ".log", len(names))
    run_lean(statements, "statements.log", statement_count)
    print(f"Checked {args.document}: {counts[0]} symbolic declarations, {links} local links, "
          f"{counts[1]} computational declarations, LaTeX references and "
          f"{statement_count} typed interface restatements; standard axioms only.")


if __name__ == "__main__":
    main()
