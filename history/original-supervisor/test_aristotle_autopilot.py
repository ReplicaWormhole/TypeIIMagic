import importlib.util
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest import mock


MODULE_PATH = Path(__file__).with_name("aristotle_autopilot.py")
SPEC = importlib.util.spec_from_file_location("aristotle_autopilot", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
AUTOPILOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUTOPILOT)


class ResponsePathTests(unittest.TestCase):
    def test_retry_uses_task_specific_archive_and_quarantine(self) -> None:
        project = {"root": "/tmp/lean-project"}
        first = {
            "packet": "/tmp/P50-normal-faithful-corner-trace.md",
            "project_id": "11111111-1111-1111-1111-111111111111",
            "task_id": "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa",
        }
        retry = {
            "packet": "/tmp/P50-normal-faithful-corner-trace.md",
            "project_id": "22222222-2222-2222-2222-222222222222",
            "task_id": "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb",
        }

        first_archive, first_quarantine = AUTOPILOT.response_paths(project, first)
        retry_archive, retry_quarantine = AUTOPILOT.response_paths(project, retry)

        self.assertNotEqual(first_archive, retry_archive)
        self.assertNotEqual(first_quarantine, retry_quarantine)
        self.assertEqual(first_archive.parent, Path(project["root"]) / "aristotle_responses")
        self.assertIn("11111111-aaaaaaaa", first_archive.name)
        self.assertIn("22222222-bbbbbbbb", retry_archive.name)
        self.assertEqual(first_archive.suffixes, [".tar", ".gz"])

    def test_download_response_reuses_only_the_exact_valid_task_archive(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = {"root": directory}
            active = {
                "packet": "/tmp/P50-normal-faithful-corner-trace.md",
                "project_id": "11111111-1111-1111-1111-111111111111",
                "task_id": "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa",
            }
            calls = []

            def fake_run(command, **_kwargs):
                calls.append(command)
                destination = Path(command[-1])
                with tarfile.open(destination, "w:gz"):
                    pass
                return subprocess.CompletedProcess(command, 0, stdout="downloaded")

            with (
                mock.patch.object(AUTOPILOT, "run", side_effect=fake_run),
                mock.patch.object(AUTOPILOT, "log_output", return_value=Path(directory) / "log"),
            ):
                first = AUTOPILOT.download_response(project, active)
                second = AUTOPILOT.download_response(project, active)

            self.assertEqual(first, second)
            self.assertEqual(len(calls), 1)
            self.assertTrue(tarfile.is_tarfile(first[0]))


class TaskStatusTests(unittest.TestCase):
    def test_out_of_budget_is_a_known_terminal_status(self) -> None:
        self.assertIn("OUT_OF_BUDGET", AUTOPILOT.TASK_STATUSES)
        self.assertIn("OUT_OF_BUDGET", AUTOPILOT.TERMINAL)

    def test_status_for_parses_out_of_budget(self) -> None:
        project_id = "11111111-1111-1111-1111-111111111111"
        task_id = "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa"
        output = f"{task_id}  P55  OUT_OF_BUDGET\n"

        with (
            mock.patch.object(
                AUTOPILOT,
                "run",
                return_value=subprocess.CompletedProcess([], 0, stdout=output),
            ),
            mock.patch.object(AUTOPILOT, "log_output", return_value=Path("/tmp/task.log")),
        ):
            status, task_output, task_log = AUTOPILOT.status_for(project_id, task_id)

        self.assertEqual(status, "OUT_OF_BUDGET")
        self.assertEqual(task_output, output)
        self.assertEqual(task_log, Path("/tmp/task.log"))


if __name__ == "__main__":
    unittest.main()
