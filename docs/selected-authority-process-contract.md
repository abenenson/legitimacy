# Selected-Authority Process Contract

The selected-authority release workload is trusted same-principal tool
execution, not a sandbox. Its process gate bounds spawn, handshake, retained
streams, execution, termination, descendant reaping, pipe draining, and status
publication while the supervisor is scheduled, and its path and cleanup checks
detect ordinary mutation within their retained parent inventory. It does not
claim protection from a same-UID process that stops the supervisor or mutates
or moves accessible paths beyond that inventory; scheduler stops and hostile
same-principal filesystem mutation are outside this gate. Executable-descriptor
launch is used for regular invoked files where their invocation semantics are
stable through `/proc/self/fd`; launcher paths whose behavior depends on their
pathname retain the same-principal pathname time-of-check/time-of-use limit.

Within that boundary, one monotonic deadline begins before output creation and
spawn. Readiness and release are nonblocking, signal-aware, and covered by that
deadline. The Linux supervisor is a child subreaper. It inventories descendant
PID/start-time identities through procfs, reaps with `waitpid(-1)`, repeatedly
signals newly observed trees during TERM and KILL phases, and treats success as
valid only when the original process group and every observed or adopted
descendant are absent, both streams reached EOF, and status publication reports
no cleanup error. Retained stdout and stderr are capped incrementally at their
exact declared byte limits.

The selected gate begins and ends at the same exact HEAD and tree with an empty
Git status, including untracked files. It binds the active launcher bytes, the
resolved rustc and Cargo version output and executable digests, the selected
source manifest, the compiled test binary, enumeration, execution, and case
manifest into its internal witness. Scratch roots retain parent and inode
identities, are inventoried after execution, and are removed explicitly on
ordinary and error returns; cleanup failure is terminal.
