# docs/ — research, plans, and progress

This tree is the project's **durable record** and crash-recovery point for the
Oseledets formalization workflow (see `../PROMPT.md`). Everything an agent needs
to resume work after a restart lives here and is committed alongside the code.

| Folder | Holds |
|---|---|
| `research/` | Scraped sources (PDFs, notes), surveys, and the understanding of the theorem and its proof route. |
| `plan/` | The dependency map and the phased, top-down implementation plan. |
| `progress/` | A single living **state** document — current target, what's done, current phase, what's next, and where the open `sorry`s are. Written to be resumable from alone. |

The folders are populated by the workflow as it runs; they start empty.
