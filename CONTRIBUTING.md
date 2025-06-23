# Contributing to the FLT Project

Thank you for your interest in contributing to the FLT Project!
This guide provides detailed instructions on how to effectively and efficiently contribute to the project.

## Project Coordination

The project is managed using a [GitHub project dashboard](https://github.com/orgs/ImperialCollegeLondon/projects/102), which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) from forks. PRs correspond to specific tasks outlined in the project's issues. The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements.

### 2. Claiming a Task

- To claim a task, comment the single word `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed` column.
- If you decide not to work on a task after claiming it, comment the single word `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should fork the project and also create a new branch from the `main` branch to develop your solution. Please try and avoid making PRs from `main` as for technical reasons this makes them slightly harder to review.

> [!WARNING]
> Before pushing any changes, you have the following options:
>
> - You might want to install the git pre-push hook by running:
>
>   ```bash
>   scripts/install_pre-push.sh
>   ```
>   This will automatically run checks before every push, reducing the risk of CI check failures.
>
> - You can manually run the following script before pushing, reducing the risk of CI check failures:
>
>   ```bash
>   scripts/run_before_push.sh
>   ```
>   This requires manual execution and won't stop the push if skipped.
>
> - You may push your changes without any safeguards, increasing the risk of CI check failures.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from the working branch of your fork to the project’s `main` branch.
- After submitting the PR, comment `propose #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment the single phrase `withdraw #PR_NUMBER` on the issue. The task will return to the `Claimed` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Review Process

- After finishing the task and ensuring your PR is ready for review, comment `awaiting-review` on the PR. This will add the `awaiting-review` label to your PR and move the task from `In Progress` to the `In Review` column of the dashboard.
 The project maintainers will review the PR. They may request changes, approve the PR, or provide feedback. If they comment `awaiting-author`, this will add the `awaiting-author` label to your PR.
 When you've responded, comment `awaiting-review` again to remove it and add the `awaiting-review` tag again.

### 7. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.

### Additional Guidelines and Notes

1. Please adhere to the issue claiming process. If an issue is already assigned to another contributor, refrain from working on it without prior communication with the current claimant. This ensures a collaborative and respectful workflow that values each contributor’s efforts.
2. Be aware that this contribution process is still in an experimental phase. As a result, occasional issues and inefficiencies may arise. We are committed to continuously refining the process, and your constructive feedback is highly appreciated. You can share your thoughts and suggestions on the [Lean Zulip chat channel](https://leanprover.zulipchat.com/#narrow/stream/416277-FLT).
3. Until the integration of sufficient CI automation, the management of the project dashboard is handled manually by the maintainers. We ask for your patience and understanding as we work to keep the process running smoothly.
