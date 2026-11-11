#!/usr/bin/env python3
"""Focused tests for plan expansion and dependency eligibility."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("aristotle_autopilot", HERE / "aristotle_autopilot.py")
assert SPEC is not None and SPEC.loader is not None
AUTOPILOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUTOPILOT)


class PlanGraphTest(unittest.TestCase):
    def setUp(self) -> None:
        self.jobs = AUTOPILOT.expanded_projects(AUTOPILOT.read_config())
        self.plan_jobs = [job for job in self.jobs if job.get("package_id")]

    def job(self, package_id: str) -> dict:
        return next(job for job in self.plan_jobs if job["package_id"] == package_id)

    def test_exact_plan_packages_are_configured(self) -> None:
        self.assertEqual(
            [job["package_id"] for job in self.plan_jobs],
            ["P47", "P48", "P49", "P49A", "P49B", "P49C"]
            + [f"P{number}" for number in range(50, 62)],
        )

    def test_initial_ready_wave_is_exact(self) -> None:
        ready = [
            job["package_id"]
            for job in self.plan_jobs
            if not job.get("depends_on") and job.get("enabled", True)
        ]
        self.assertEqual(ready, ["P47", "P48", "P52", "P54"])

    def test_dependencies_require_accepted_advance(self) -> None:
        state = {
            "projects": {
                "one": {
                    "completed": [
                        {"package_id": "P47", "decision": "advance"},
                        {"package_id": "P48", "decision": "halt"},
                    ]
                }
            }
        }
        self.assertEqual(AUTOPILOT.missing_dependencies(self.job("P49"), state), ["P48"])
        state["projects"]["one"]["completed"][1]["decision"] = "advance"
        self.assertEqual(AUTOPILOT.missing_dependencies(self.job("P49"), state), [])

    def test_optional_packages_are_disabled(self) -> None:
        self.assertFalse(self.job("P60")["enabled"])
        self.assertFalse(self.job("P61")["enabled"])

    def test_corner_trace_waits_for_kaplansky(self) -> None:
        self.assertEqual(self.job("P50")["depends_on"], ["P49", "P49C"])

    def test_dependency_graph_is_acyclic_and_internal(self) -> None:
        remaining = {job["package_id"]: set(job.get("depends_on", [])) for job in self.plan_jobs}
        all_ids = set(remaining)
        self.assertTrue(all(dependencies <= all_ids for dependencies in remaining.values()))
        resolved: set[str] = set()
        while remaining:
            ready = {package_id for package_id, dependencies in remaining.items() if dependencies <= resolved}
            self.assertTrue(ready, f"dependency cycle: {remaining}")
            resolved.update(ready)
            for package_id in ready:
                del remaining[package_id]

    def test_configured_lane_matches_packet(self) -> None:
        for job in self.plan_jobs:
            text = AUTOPILOT.packet_path(job, 0).read_text()
            self.assertIn(f"Lane `{job['plan_lane']}`", text, job["package_id"])

    def test_mobile_alert_names_packet_lane_and_reason(self) -> None:
        message = AUTOPILOT.telegram_message(
            {"id": "stabilizer_two_lane_p47", "plan_lane": "G"},
            "P47",
            "Codex recorded a partial result.",
        )
        self.assertIn("P47", message)
        self.assertIn("Lane G", message)
        self.assertIn("partial result", message)

    def test_every_packet_exists_and_declares_alignment(self) -> None:
        for job in self.plan_jobs:
            packet = AUTOPILOT.packet_path(job, 0)
            self.assertTrue(packet.is_file(), packet)
            text = packet.read_text()
            self.assertIn("## Context declaration", text, packet)
            self.assertIn("## Plan alignment", text, packet)
            self.assertIn("Forbidden downstream claims", text, packet)


if __name__ == "__main__":
    unittest.main()
