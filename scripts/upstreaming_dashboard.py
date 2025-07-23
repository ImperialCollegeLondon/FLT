#!/usr/bin/env python3
# Copyright (c) 2024 Yaël Dillies, Javier Lopez-Contreras. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

"""
This script parse the aggregate json file and filters all PRs which touch some given files.
"""

import json
import os
import pathlib
import subprocess
from typing import Any

# To customize
MODULE = "FLT"
REPOSITORY = "ImperialCollegeLondon/FLT"
BRANCH = "main"
FOLDER_PATH = "./docs/_includes"

QUEUEBOARD = (
    "https://raw.githubusercontent.com/leanprover-community/queueboard/refs/"
    "heads/master/processed_data/open_pr_data.json")
PR_SYMBOL = '<svg class="octicon octicon-git-pull-request open color-fg-open mr-1" title="Open" viewBox="0 0 16 16" version="1.1" width="16" height="16" aria-hidden="true"><path d="M1.5 3.25a2.25 2.25 0 1 1 3 2.122v5.256a2.251 2.251 0 1 1-1.5 0V5.372A2.25 2.25 0 0 1 1.5 3.25Zm5.677-.177L9.573.677A.25.25 0 0 1 10 .854V2.5h1A2.5 2.5 0 0 1 13.5 5v5.628a2.251 2.251 0 1 1-1.5 0V5a1 1 0 0 0-1-1h-1v1.646a.25.25 0 0 1-.427.177L7.177 3.427a.25.25 0 0 1 0-.354ZM3.75 2.5a.75.75 0 1 0 0 1.5.75.75 0 0 0 0-1.5Zm0 9.5a.75.75 0 1 0 0 1.5.75.75 0 0 0 0-1.5Zm8.25.75a.75.75 0 1 0 1.5 0 .75.75 0 0 0-1.5 0Z"></path></svg>'

def main():
    pr_file = subprocess.run(["curl", QUEUEBOARD], capture_output=True, text=True)
    pr_json = json.loads(pr_file.stdout)["pr_statusses"]
    pr_dict = {pr["number"]: pr for pr in pr_json}

    file_touched_pr: dict[str, list[Any]] = {}
    for pr in pr_dict:
        for file in pr_dict[pr]["files"]:
            pr_data = {
                "number" : pr,
                "title" : pr_dict[pr]["title"],
                "num_files": len(pr_dict[pr]["files"]),
                "is_draft": pr_dict[pr]["is_draft"]
            }
            if file not in file_touched_pr: file_touched_pr[file] = [pr_data]
            else: file_touched_pr[file].append(pr_data)

    project_files: dict[str, Any] = {}
    for entry in pathlib.Path(MODULE).rglob("*.lean"):
        code = None
        with open(entry, 'r') as reader:
            code = reader.read()
        entry = str(entry)
        file = "/".join(entry.split("/")[1:])
        project_files[entry] = {
            "prs" : [] if file not in file_touched_pr else file_touched_pr[file],
            "num_sorries" : code.count("sorry"),
            "depends" : f"import {MODULE}" in code
        }

    if not os.path.exists(FOLDER_PATH):
        os.makedirs(FOLDER_PATH)

    with open(f"{FOLDER_PATH}/ready_to_upstream.md", 'w+') as writer:
        for file_path in project_files:
            if project_files[file_path]["num_sorries"] > 0:
                continue
            if project_files[file_path]["depends"]:
                continue
            module_name = file_path.replace('/','.')[:-5]
            writer.write(f"* [`{module_name}`](https://github.com/{REPOSITORY}/blob/{BRANCH}/{file_path})\n")
            for pr in project_files[file_path]["prs"]:
                if pr["title"][:4] == "perf":
                    continue
                if pr["is_draft"]:
                    continue

                writer.write(f"  * [{PR_SYMBOL} {pr['title']} #{pr['number']}]")
                writer.write(f"(https://github.com/leanprover-community/mathlib4/pull/{pr['number']})\n")

    with open(f"{FOLDER_PATH}/easy_to_unlock.md", 'w+') as writer:
        for file_path in project_files:
            if project_files[file_path]["num_sorries"] == 0:
                continue
            if project_files[file_path]["depends"]:
                continue
            num_sorries = project_files[file_path]["num_sorries"]
            module_name = file_path.replace('/','.')[:-5]
            if num_sorries == 1:
                sorries = f"{num_sorries} sorry"
            else:
                sorries = f"{num_sorries} sorries"
            writer.write(f"* [`{module_name}`](https://github.com/{REPOSITORY}/blob/{BRANCH}/{file_path}) {sorries}\n")

main()
