# Contributing to the FLT Project

Thank you for your interest in contributing to the FLT Project! This guide provides detailed instructions on how to effectively and efficiently contribute to the project.

## Project Coordination

The project is managed using a [GitHub project dashboard](#), which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) that correspond to specific tasks outlined in the project's issues. The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed Tasks` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements.

### 2. Claiming a Task

- To claim a task, comment `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed Tasks` column.
- You may only claim one task at a time. If you decide not to work on a task after claiming it, comment `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed Tasks` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should create a new branch from the `main` branch to develop your solution.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from your working branch to the project’s `main` branch.
- After submitting the PR, comment `propose PR #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment `withdraw PR #PR_NUMBER` on the issue. The task will return to the `Claimed Tasks` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose PR #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Review Process

- After finishing the task and ensuring your PR is ready for review, comment `awaiting-review` on the PR. This will add the `awaiting-review` label to your PR and move the task from `In Progress` to the `In Review` column of the dashboard.
- The project maintainers will review the PR. They may request changes, approve the PR, or provide feedback.

### 7. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed Tasks` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.
