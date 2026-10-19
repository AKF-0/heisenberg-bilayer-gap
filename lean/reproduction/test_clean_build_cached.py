"""Small non-compiling tests for the clean-build driver's safety boundaries."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("clean_build", Path(__file__).with_name("clean_build_cached.py"))
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class DriverTests(unittest.TestCase):
    def test_nested_comments(self):
        text = "/- import Wrong /- import Wrong2 -/ -/\nimport Dressed.Real\n-- import Wrong3\n"
        cleaned = driver.without_comments(text)
        self.assertNotIn("Wrong", cleaned)
        self.assertIn("import Dressed.Real", cleaned)

    def test_comment_text_inside_string_is_preserved(self):
        self.assertEqual(driver.without_comments('def x := "-- /- still a string"'),
                         'def x := "-- /- still a string"')

    def test_unclosed_comment_fails(self):
        with self.assertRaises(RuntimeError):
            driver.without_comments("/- unfinished")

    def test_imports_ignore_comments_and_stop_at_commands(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "Example.lean"
            source.write_text("/- header -/\nimport Dressed.A Gap.B\n\nimport Lean\nnamespace X\n")
            self.assertEqual(driver.imports(source), ["Dressed.A", "Gap.B", "Lean"])

    def test_unsupported_import_syntax_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "Example.lean"
            source.write_text("import Dressed.A; #eval 2\n")
            with self.assertRaises(RuntimeError):
                driver.imports(source)

    def test_path_escape_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "snapshot"
            root.mkdir()
            (Path(tmp) / "outside").write_text("not in the snapshot")
            with self.assertRaises(RuntimeError):
                driver.inside(root.resolve(), "../outside")

    def test_symlink_escape_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "snapshot"
            root.mkdir()
            outside = Path(tmp) / "outside"
            outside.write_text("not in the snapshot")
            (root / "alias").symlink_to(outside)
            with self.assertRaises(RuntimeError):
                driver.inside(root.resolve(), "alias")

    def test_audit_checks_origin_and_nonempty_counts(self):
        source = driver.audit_source(["Dressed.A", "Gap.B"], ["Dressed.A"])
        self.assertIn("env.getModuleIdxFor?", source)
        self.assertIn("if names.isEmpty", source)
        self.assertIn("declaringModules.contains m && count == 0", source)
        self.assertIn("Unapproved axiom", source)
        self.assertNotIn("isPrefixOf", source)
        self.assertIn("Array.replicate moduleNames.size false", source)
        self.assertIn("counts := counts.set!", source)
        self.assertNotIn("localModules.contains moduleNames", source)
        self.assertNotIn("entries.filter", source)


if __name__ == "__main__":
    unittest.main()
