import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "engine", ROOT / "workflow/aristotle_autopilot.py"
)
engine = importlib.util.module_from_spec(spec)
spec.loader.exec_module(engine)


class ContinuedLoopTests(unittest.TestCase):
    def test_exported_config_is_portable(self):
        for project in engine.read_config()["project"]:
            for key in ["root", "paper_root", "task_root"]:
                path = Path(project[key])
                self.assertTrue(path.is_absolute())
                self.assertTrue(path.is_relative_to(ROOT))
                self.assertTrue(path.is_dir())

    def test_missing_runtime_uses_historical_state(self):
        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(engine, "STATE", Path(tmp) / "state.json"),
        ):
            state = engine.read_state()
        self.assertEqual(len(state["projects"]["finite_fiber"]["completed"]), 9)
        self.assertTrue(state["projects"]["stabilizer_two_lane_p57c"]["halted"])
        self.assertTrue(state["projects"]["stabilizer_two_lane_p59b"]["halted"])
        path = state["projects"]["finite_fiber"]["completed"][-1]["final"]
        self.assertTrue(Path(path).is_file())

    def test_dry_run_does_not_call_commands_or_create_runtime(self):
        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(engine, "STATE", Path(tmp) / "state.json"),
            mock.patch.object(
                engine, "run", side_effect=AssertionError("external command")
            ),
        ):
            with mock.patch("sys.argv", ["engine", "--once", "--dry-run"]):
                self.assertEqual(engine.main(), 0)
            self.assertFalse((Path(tmp) / "state.json").exists())

    def cycle(self, decision):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            packet = root / "NEXT.md"
            packet.write_text("prepared task")
            final = root / "final.md"
            final.write_text(
                "AUTOPILOT_ACCEPTED: yes\nAUTOPILOT_DECISION: " + decision + "\n"
            )
            active = {
                "packet": str(packet),
                "queue_index": 0,
                "project_id": "p",
                "task_id": "t",
                "package_id": "FIRST",
            }
            lane = {"active": active, "next_index": 1, "completed": [], "halted": False}
            state = {"projects": {"lane": lane}}
            project = {
                "id": "lane",
                "queue": ["NEXT.md", "NEXT.md"],
                "task_root": str(root),
                "root": str(root),
            }
            with (
                mock.patch.object(engine, "write_state"),
                mock.patch.object(
                    engine,
                    "status_for",
                    return_value=("COMPLETE", "remote output", root / "status.log"),
                ),
                mock.patch.object(
                    engine, "invoke_codex", return_value=(0, final, root / "prompt.md")
                ),
                mock.patch.object(
                    engine,
                    "submit",
                    return_value=("new-project", "new-task", root / "submit.log"),
                ) as submit,
            ):
                engine.process_project(
                    project, state, {}, dry_run=False, no_codex=False, timeout=0
                )
                return lane, submit.call_count

    def test_real_state_machine_advances_and_submits_next_packet(self):
        lane, calls = self.cycle("advance")
        self.assertEqual(calls, 1)
        self.assertEqual(lane["completed"][0]["decision"], "advance")
        self.assertEqual(lane["active"]["task_id"], "new-task")

    def test_real_state_machine_halts_without_submitting(self):
        lane, calls = self.cycle("halt")
        self.assertEqual(calls, 0)
        self.assertTrue(lane["halted"])

    def test_dependencies_require_an_accepted_advance(self):
        state = {
            "projects": {
                "prior": {"completed": [{"package_id": "A", "decision": "halt"}]}
            }
        }
        self.assertEqual(
            engine.missing_dependencies({"depends_on": ["A"]}, state), ["A"]
        )
        state["projects"]["prior"]["completed"][0]["decision"] = "advance"
        self.assertEqual(engine.missing_dependencies({"depends_on": ["A"]}, state), [])

    def test_scope_still_contains_both_original_programs(self):
        jobs = engine.expanded_projects(engine.read_config())
        self.assertEqual(
            {p.get("program_id", p["id"]) for p in jobs},
            {"finite_fiber", "stabilizer_two_lane"},
        )
        ids = {p.get("package_id") for p in jobs}
        self.assertTrue({"P57C", "P59B", "P59R", "P59T"} <= ids)


if __name__ == "__main__":
    unittest.main()


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "typeii_cli", ROOT / "scripts/typeiimagic.py"
        )
        self.cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.cli)

    def test_resume_preserves_prior_halts_and_writes_no_submission(self):
        e = self.cli.engine
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp)
            with (
                mock.patch.object(e, "RUNTIME", runtime),
                mock.patch.object(e, "LOCK", runtime / "lock"),
                mock.patch.object(e, "STATE", runtime / "state.json"),
                mock.patch.object(
                    e, "run", side_effect=AssertionError("no external commands")
                ),
            ):
                self.cli.resume(
                    "P57C",
                    "Reviewed missing completed-ITP bridge and source locators",
                    True,
                )
                state = e.read_state()
                lane = state["projects"]["stabilizer_two_lane_p57c"]
                self.assertFalse(lane["halted"])
                self.assertEqual(lane["completed"][0]["decision"], "halt")
                self.assertEqual(state["resume_events"][0]["package"], "P57C")
                self.assertEqual(lane["next_index"], 0)

    def test_resume_without_execute_is_rejected(self):
        with self.assertRaises(ValueError):
            self.cli.resume("P57C", "reviewed", False)

    def test_resume_refuses_ambiguous_old_active_tasks(self):
        e = self.cli.engine
        state = e.read_state()
        lane = state["projects"]["stabilizer_two_lane_p57c"]
        lane["active"] = {"task_id": "unresolved"}
        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(e, "RUNTIME", Path(tmp)),
            mock.patch.object(e, "LOCK", Path(tmp) / "lock"),
            mock.patch.object(e, "read_state", return_value=state),
        ):
            with self.assertRaises(ValueError):
                self.cli.resume("P57C", "reviewed", True)

    def test_inspection_status_is_offline(self):
        with mock.patch.object(
            self.cli.engine, "run", side_effect=AssertionError("no external commands")
        ):
            data = self.cli.summary()
        self.assertEqual(data["outcomes"], {"advance": 36, "halt": 4})
        self.assertEqual(
            [j["package"] for j in data["jobs"] if j["status"] == "halted"],
            ["P57C", "P59B"],
        )


class ExecutionBoundaryTests(unittest.TestCase):
    def test_real_execution_requires_opt_in(self):
        with (
            mock.patch("sys.argv", ["engine", "--once"]),
            mock.patch.object(
                engine, "run", side_effect=AssertionError("unexpected execution")
            ),
        ):
            with self.assertRaises(SystemExit) as error:
                engine.main()
        self.assertEqual(error.exception.code, 2)

    def test_runtime_paths_are_stored_portably(self):
        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(engine, "STATE", Path(tmp) / "state.json"),
        ):
            engine.write_state(
                {"projects": {"x": {"final": str(ROOT / "history/logs/review.md")}}}
            )
            saved = json.loads(engine.STATE.read_text())
            self.assertEqual(saved["projects"]["x"]["final"], "history/logs/review.md")
            self.assertEqual(
                engine.read_state()["projects"]["x"]["final"],
                str(ROOT / "history/logs/review.md"),
            )

    def test_upload_preserves_source_and_fixes_upload_only_policy_path(self):
        import shutil

        project = engine.read_config()["project"][1]
        source_policy = Path(project["root"]) / "AGENTS.md"
        original = source_policy.read_bytes()
        stage = engine.submission_stage(project)
        try:
            self.assertEqual(
                (stage / "manuscript/main.tex").read_bytes(),
                (Path(project["paper_root"]) / "main.tex").read_bytes(),
            )
            self.assertNotIn("sources/manuscript/", (stage / "AGENTS.md").read_text())
            self.assertFalse((stage / ".lake").exists())
            self.assertEqual(source_policy.read_bytes(), original)
        finally:
            shutil.rmtree(stage)
