## Reasoning about trust
1. If there are no side effects and the dependents are safe, the crate is safe.
2. If a crate has a passed audit, the crate is safe.
3. The higher the downloads, the more trustworthy the crate is.
4. The more reputable the owners, the more trustworthy the crate is.
5. The more (reputable) dependents the crate has, the more trustworthy the crate is.
6. The more stars and forks the crate repo has, the more trustworthy the crate is.
7. If a crate has passed the Rudra static analyzer, it is safe.
8. If a crate appears on RustSec, it is not safe.

## Rules for assigning weight
1. The more dubious an assumption is, the higher weight it should have.
2. Weight is a non-negative integer assigned to each assumption.
3. The weight of the assumption $(p \wedge q)\rightarrow c$ should be less than or equal to the weight of the assumptions $p \rightarrow c$ and $q \rightarrow c$ combined.

The set of assumptions themselves should be consistent.
