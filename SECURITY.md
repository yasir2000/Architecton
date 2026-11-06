# Security policy

## Status

Architecton is a research proof of concept. **The DriverPass sample API has no authentication and must only listen on loopback.** Don't deploy it to a network that other people can reach.

Formal proofs here cover Lean models under stated assumptions. They don't establish that compiled code or deployments are secure; see [assurance limits](docs/assurance.md).

## Supported versions

Only the latest commit on `main` is supported.

## Reporting a vulnerability

Please **don't open a public issue**. Report it privately through GitHub's [private vulnerability reporting](https://github.com/yasir2000/Architecton/security/advisories/new) and include:

- what is affected (file, package, workflow or proof);
- steps to reproduce or a proof of concept;
- the impact you expect.

You should get an acknowledgement within 7 days. Once a fix is ready, we'll agree a disclosure date with you, and credit you unless you prefer otherwise.

## In scope

- the evidence ledger (signature verification, revocation, content addressing);
- CI workflows and supply chain (actions, generated artifacts);
- unsound proofs, such as a hidden axiom or a statement that doesn't mean what its documentation claims.
