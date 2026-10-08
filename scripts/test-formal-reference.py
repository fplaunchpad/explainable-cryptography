#!/usr/bin/env python3
"""Negative controls for the formal-reference evidence gate."""
import importlib.util
from pathlib import Path
import unittest
import tempfile
import argparse

spec = importlib.util.spec_from_file_location(
    "reference_gate", Path(__file__).with_name("check-formal-reference.py"))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


DOCUMENT = "reference"


class ReferenceGateTests(unittest.TestCase):
    def test_current_document(self):
        tex = gate.DOC.read_text()
        self.assertTrue(gate.anchors(tex, "companchor", gate.ROOT / "ExplainableCrypto/Helios/Computational"))
        if DOCUMENT == "reference":
            self.assertTrue(gate.anchors(tex))
        self.assertGreater(gate.validate_links(tex), 0)
        if DOCUMENT == "reference":
            gate.validate_snippets(tex)
        gate.validate_language(tex, DOCUMENT)

    def test_stale_theorem_transcription(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name, content in gate.source_snippets().items():
                (directory / name).write_text(content)
            gate.validate_snippets((gate.ROOT / "docs/formal-reference/main.tex").read_text(), directory)
            path = directory / "BallotSecrecy.lean"
            path.write_text(path.read_text().replace("    (hreject :", "    (removed :"))
            with self.assertRaisesRegex(ValueError, "Stale"):
                gate.validate_snippets((gate.ROOT / "docs/formal-reference/main.tex").read_text(), directory)

    def test_missing_source(self):
        with self.assertRaisesRegex(ValueError, "Missing source"):
            gate.anchors(r"\begin{document}\anchor{AbsentReferenceModule}{Accepted}")

    def test_malformed_anchor(self):
        with self.assertRaisesRegex(ValueError, "malformed"):
            gate.anchors(r"\begin{document}\anchor{Symbolic/Ballot}{Accepted")

    def test_dangling_reference(self):
        with self.assertRaisesRegex(ValueError, "Unresolved LaTeX"):
            gate.validate_links(r"\ref{absent}")

    def test_axiom_gate(self):
        gate.audit_log("'ok' depends on axioms: [propext, Quot.sound]", 1)
        gate.audit_log("'ok' does not depend on any axioms", 1)
        for bad in ["'bad' depends on axioms: [unsound]",
                    "'bad' depends on axioms: [sorryAx]", ""]:
            with self.assertRaises(ValueError):
                gate.audit_log(bad, 1)

    def test_deferred_citation(self):
        gate.validate_scope(["ExplainableCrypto.Helios.Computational.ElectionSecurityFamily"], "")
        for modules, statement in [
            (["ExplainableCrypto.Helios.Computational.NativeAdaptiveCost"], ""),
            ([], "import ExplainableCrypto.Helios.Computational.NativeAdaptiveCost")]:
            with self.assertRaisesRegex(ValueError, "deferred"):
                gate.validate_scope(modules, statement)

    def test_status_language(self):
        for phrase in ["3/3 milestones complete", "C5 remains partial", "positive controls"]:
            with self.assertRaisesRegex(ValueError, "internal vocabulary"):
                gate.validate_language(r"\begin{document}" + phrase, "reference")
        for phrase in ["The secrecy theorem remains open.", "No checkpoint closes here.",
                       "No efficiency certificate is assumed in the intended endpoint."]:
            with self.assertRaisesRegex(ValueError, "obsolete status"):
                gate.validate_language(r"\begin{document}" + phrase, "catalogue")
        gate.validate_language(r"\begin{document}Historically, this fragment did not establish secrecy.", "catalogue")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--document", choices=gate.DOCUMENTS, default="reference")
    args, remaining = parser.parse_known_args()
    DOCUMENT = args.document
    gate.DOC = gate.ROOT / "docs/formal-reference" / gate.DOCUMENTS[DOCUMENT][0]
    unittest.main(argv=[__file__, *remaining])
