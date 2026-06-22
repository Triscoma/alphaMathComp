'''
Construit l'arbre de treefinement.
'''

import os
import json
import re
import pickle
from queue import PriorityQueue
from pytanque import Pytanque, PytanqueMode
from openai import AsyncOpenAI
from parsing.dependencies import dependencies_in_goal, dependencies_to_str
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FutureTimeoutError
import time
import random
import asyncio

# ---------------------------------------------------------------------------
# parameters
# ---------------------------------------------------------------------------
arity = 3
beam_size = 2
iter_max = 5
nb_examples = 5

max_sample_size = 50

# Outer loop: how many concurrent Pytanque STDIO processes / theorems at once.
outer_max_workers = 16

# Timeout (seconds) for a single Pytanque call (run / goals / get_state_at_pos).
# Chosen defensively: we have not verified abandon-and-continue is safe on the
# underlying pipe, so a timeout means "treat this client as dead", not "retry
# on the same client".
pytanque_call_timeout = 30

"""
alpha = 1
beta = 1
def penalty(error, depth) :
    return alpha * error + beta * depth
"""
#model = "openai/gpt-4.1" # gros modèle
model = "mistralai/mistral-small-2603"
#model = "nvidia/nemotron-3-nano-30b-a3b:free" # modèle de test


with open('data/output/train_tmp/filepath.json') as filepath_json :
    filepath = json.load(filepath_json)

with open('data/output/train_tmp/position.json') as position_json :
    position = json.load(position_json)

with open('data/output/train_tmp/tactic.json') as tactic_json :
    tactic = json.load(tactic_json)

with open('data/output/train_tmp/next_tactic.json') as next_tactic_json :
    next_tactic = json.load(next_tactic_json)

with open('data/output/train_tmp/statement.json') as statement_json :
    statement = json.load(statement_json)

with open('data/output/train_tmp/theorem.json') as theorem_json :
    theorem = json.load(theorem_json)

with open('data/output.json') as output_json :
    data = json.load(output_json)

with open('confidential.json') as confidential_json :
    confidential = json.load(confidential_json)
    API_KEY = confidential["API_KEY"]


async_chatbot = AsyncOpenAI(
        base_url="https://openrouter.ai/api/v1",
        api_key=API_KEY,
    )


def parse_tactics(text) :
    #print("PARSE_INPUT : ", text)
    ans = []
    buffer = ""
    for i in range(len(text)) :
        if (len(ans) == arity):
            break
        buffer += text[i]
        if text[i] == '.' :
            buffer = buffer.strip()
            if (len(buffer) <= 1) :
                buffer = "idtac."
            ans.append(buffer)
            buffer = ""
    if (len(ans) < arity) :
        ans.append("idtac.")
    return ans


# ---------------------------------------------------------------------------
# PytanqueGuard
#
# Wraps a single Pytanque client and forces every call against it through a
# single-worker executor. A one-worker pool gives us two things a plain
# threading.Lock did not:
#   - the same serialization guarantee (only one Pytanque call in flight at
#     a time for this client), and
#   - a `future.result(timeout=...)` we can use to bail out of a call that
#     hangs (your own comment flags client.goals as doing this).
#
# RETRY POLICY: on a timeout, we retry the SAME call on the SAME
# client/process, up to `max_call_retries` times, on the assumption that the
# pipe survives an abandoned call and the call was just slow rather than
# wedged. We abandon the Future each time (the executor is single-worker, so
# an abandoned-but-still-running call's worker thread is occupied; a retry
# submitted to the same executor will queue behind it rather than run
# concurrently -- if the original call truly never returns, each retry will
# itself wait out the full timeout before getting a turn). This is the
# tradeoff of reusing the same process: simpler recovery, but a genuinely
# wedged call costs `max_call_retries * timeout` before we give up on it.
# Only after retries are exhausted do we mark the client poisoned and stop
# trusting it -- this is the safety net in case "abandon and continue" turns
# out not to be safe after all.
# ---------------------------------------------------------------------------
max_call_retries = 3

class PytanqueGuard:
    def __init__(self, client):
        self.client = client
        self._executor = ThreadPoolExecutor(max_workers=1)
        self.poisoned = False

    def _call(self, fn, *args, timeout=pytanque_call_timeout, retries=max_call_retries, **kwargs):
        if self.poisoned:
            raise RuntimeError("PytanqueGuard: client is poisoned, refusing call")

        name = getattr(fn, "__name__", fn)
        last_timeout_msg = None
        for attempt in range(1, retries + 1):
            future = self._executor.submit(fn, *args, **kwargs)
            try:
                return future.result(timeout=timeout)
            except FutureTimeoutError:
                # We never await/cancel `future` here: the worker thread
                # inside self._executor may still be stuck running the
                # original call. We just stop waiting on it and, per the
                # reuse-same-client policy, submit a fresh attempt to the
                # same single-worker executor (which will queue behind the
                # abandoned one if it's still running).
                last_timeout_msg = (
                    f"Pytanque call {name} timed out after {timeout}s "
                    f"(attempt {attempt}/{retries})"
                )
                print(f"[PytanqueGuard] {last_timeout_msg}, retrying on same client")
                continue
            except Exception:
                # Any other failure from the underlying call: surface it, but
                # don't poison automatically, since these are "normal" tactic
                # errors (e.g. invalid tactic) that the tree search is
                # designed to recover from.
                raise

        # Retries exhausted: stop trusting this client.
        self.poisoned = True
        raise TimeoutError(f"{last_timeout_msg}; retries exhausted, client marked poisoned")

    def get_state_at_pos(self, file, line, char):
        return self._call(self.client.get_state_at_pos, file, line, char)

    def goals(self, proof_state):
        return self._call(self.client.goals, proof_state)

    def run(self, proof_state, tactic_str):
        return self._call(self.client.run, proof_state, tactic_str)

    def shutdown(self):
        # Don't wait on a worker that may be stuck forever inside Pytanque.
        self._executor.shutdown(wait=False, cancel_futures=False)


def make_guarded_client(cm_factory):
    """
    cm_factory: a zero-arg callable returning a fresh Pytanque context manager,
    e.g. `lambda: Pytanque(mode=PytanqueMode.STDIO)`.
    Returns (guard, raw_context_manager) so the caller can __exit__ it later.
    """
    cm = cm_factory()
    client = cm.__enter__()
    return PytanqueGuard(client), cm


# ---------------------------------------------------------------------------
# Examples used in the LLM prompt. Built once at import time using a plain,
# short-lived Pytanque client (no concurrency involved here, so no guard
# needed).
# ---------------------------------------------------------------------------
examples = []
def init_examples(client) :
    example_lemmas = set()
    while len(example_lemmas) <= nb_examples :
        tactic_number = str(len(examples))
        lemma = theorem[tactic_number]
        example_lemmas.add(lemma)
        file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
        line, char = pos["line"], pos["character"]
        goal = client.goals(client.get_state_at_pos(file, line, char))[0].pp
        examples.append({"goal" : goal, "tactic tried" : None, "error" : None, "tactic corrected" : tactic[tactic_number]})

with Pytanque(mode=PytanqueMode.STDIO) as client :
    init_examples(client)

good_proof_steps = examples


# ---------------------------------------------------------------------------
# LLM querying, async. No thread pool needed: this is pure I/O-bound waiting
# on the OpenRouter HTTP call, so asyncio.gather across beam nodes gives real
# concurrency without spinning up OS threads just to block on a socket.
# ---------------------------------------------------------------------------
async def ask_llm_async(guard, prev_tactic, proof_st, error, feedback) :
    # client.goals must still go through the guard (serialized, timeout-
    # guarded Pytanque access) even though this function is async: Pytanque
    # itself has no native async API. Critically, we dispatch the blocking
    # guard.goals() call via run_in_executor rather than calling it directly:
    # this function runs on the tree's single event-loop thread, and a
    # direct call would block that whole event loop (and therefore every
    # other concurrently-gathered beam branch) for up to
    # pytanque_call_timeout seconds. run_in_executor hands the wait off to a
    # worker thread so other coroutines on this loop can keep progressing
    # (in particular, their own goals() calls queueing on the guard's
    # single-worker executor) while this one is in flight.
    loop = asyncio.get_event_loop()
    raw_goal = await loop.run_in_executor(None, guard.goals, proof_st)
    goal = raw_goal[0].pp

    prompt = "Here is a goal in coq (mathematical components): \n\n"
    prompt += goal
    prompt += "\n\nWrite the next command you would use to solve it.\n"
    prompt += f"Propose up to {arity} options.\n"
    prompt += "Don't write anything else, and don't annotate your answer. Write eache proposal on a new line."
    prompt += "Each of your proposal should end by a point.\n"

    prompt += "\n\nTo help you, here are some examples of proof steps in mathcomp for a given goal statement:\n"
    for ex in random.sample(good_proof_steps, max(5, min(max_sample_size, len(good_proof_steps)))):
        prompt += "\nGoal : \n" + ex["goal"] + "\n"
        if (ex["error"] is None) :
            prompt += "\nNext tactic : " + ex["tactic corrected"] + "\n"
        else :
            prompt += "\nUnsuccessful tactic : " + ex["tactic tried"]
            prompt += "\nError : " + ex["error"]
            prompt += "\nTactic corrected : " + ex["tactic corrected"] + "\n"
    if prev_tactic != None :
        prompt += "\nThe last command you tried is :\n" + prev_tactic
    if (error != None) :
        prompt += "\nbut got the error : \n" + error + "\nCorrect your answer.\n"

    prompt += "\nSo far, you got the following feedback (may have been truncated if longer than 50 lines) :\n"
    for level, message in feedback:
        prompt += f"Level {level}: {message}\n"
    prompt += "\nYou can use commands like 'Check', 'Search', etc. if you need more information about the context.\n"

    try :
        response = await async_chatbot.responses.create(
                model=model,
                input=prompt
                )
        tacs = parse_tactics(response.output_text)
    except Exception as err:
        print("Error while querying llm : ", err)
        tacs = ["idtac."]
    return tacs


# ---------------------------------------------------------------------------
# Tree construction for a single theorem. Runs inside one asyncio event loop
# (driven via asyncio.run from the outer thread pool worker). One guard /
# one Pytanque process per theorem, exactly as before, but:
#   - beam expansion gathers all LLM calls concurrently (asyncio.gather)
#   - Pytanque calls (client.run) stay strictly sequential, since the
#     protocol requires it, but are timeout-guarded so a hang can't freeze
#     the tree forever.
#   - if the guard gets poisoned mid-tree, the tree is abandoned (treated as
#     a failure for this attempt) and the caller is responsible for
#     recreating a fresh client/guard for that theorem if it wants to retry.
# ---------------------------------------------------------------------------
async def make_tree(guard, tactic_number_) :
    print("tactic_number : ", tactic_number_)
    tactic_number = str(tactic_number_)
    tree = [[]]
    parent = [0]
    depth = [0]
    proof_state = []
    tactic_tried = [None]
    error = [None]
    node_feedback = [[]]

    file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
    line, char = pos["line"], pos["character"]
    loop = asyncio.get_event_loop()
    proof_state.append(await loop.run_in_executor(None, guard.get_state_at_pos, file, line, char))

    pq = PriorityQueue() # couples of (penalty, node_id)
    pq.put((0, 0))

    def collect_success_steps(new_node) :
        '''Retrieve the correction steps once a node reaches proof_finished.
        Called only once, right before make_tree returns, so there are no
        sibling coroutines left to starve -- unlike the calls inside
        make_new_branches, this one is intentionally left as a direct
        (blocking) guard call rather than routed through run_in_executor.'''
        steps = []
        n = new_node
        while n != 0 :
            n_ = parent[n]
            while error[n_] != None :
                n_ = parent[n_]
            def dfs(u) :
                goal = guard.goals(proof_state[u])[0].pp
                steps.append({"goal" : goal, "tactic tried" : tactic_tried[u], "error" : error[u], "tactic corrected" : tactic_tried[n]})
                for v in tree[u] :
                    if (error[v] != None) :
                        dfs(v)
            dfs(n_)
            n = n_
        return steps

    async def make_new_branches(pen, node) :
        '''Generate up to `arity` children of node. Returns success steps if
        one of the resulting tactics finished the proof, else [].'''
        proof_st = proof_state[node]
        new_feedback = node_feedback[node][:40] + proof_st.feedback[:50]

        tacs = await ask_llm_async(guard, tactic_tried[node], proof_st, error[node], new_feedback)
        print("TACS :", tacs)

        # Pytanque calls must stay sequential (single STDIO process per
        # theorem), so the guard's single-worker executor still serializes
        # them. But this coroutine runs concurrently with sibling branches
        # via asyncio.gather, so guard.run() is dispatched through
        # run_in_executor rather than called directly: a direct call would
        # block this whole event loop for the duration of the call (up to pytanque_call_timeout on a hang), starving every other
        # gathered branch even though their work is independent.
        loop = asyncio.get_event_loop()
        for tac in tacs :
            try :
                new_state = await loop.run_in_executor(None, guard.run, proof_st, tac)
                new_error = None
            except TimeoutError :
                # guard is now poisoned; propagate so the whole tree attempt
                # is abandoned rather than silently corrupting the search.
                raise
            except Exception as err :
                new_state = proof_st
                new_error = str(err)

            new_node = len(parent)
            tree.append([])
            tree[node].append(new_node)
            parent.append(node)
            depth.append(depth[node] + 1)
            proof_state.append(new_state)
            tactic_tried.append(tac)
            error.append(new_error)
            node_feedback.append(new_feedback)

            if proof_state[new_node].proof_finished :
                return collect_success_steps(new_node)
            else :
                pq.put((pen + (0 if error[new_node] is None else 1), new_node))
        return []

    for it in range(iter_max) :
        beam_nodes = []
        for _ in range(beam_size) :
            if pq.empty() :
                break
            beam_nodes.append(pq.get())

        if not beam_nodes :
            break

        # Real concurrency here: each beam branch's LLM call runs
        # concurrently. The Pytanque .run() calls inside each branch are
        # still serialized by the guard, but that serialization is now just
        # "wait your turn on one worker thread", not "block an OS thread
        # doing nothing while waiting on the LLM".
        results = await asyncio.gather(
            *(make_new_branches(pen, node) for pen, node in beam_nodes),
            return_exceptions=True,
        )

        for steps in results :
            if isinstance(steps, TimeoutError) :
                # This tree's client is poisoned; stop trying to use it.
                print(tactic_number, "-- finished(failure: pytanque timeout, client poisoned)")
                return []
            if isinstance(steps, BaseException) :
                # Unexpected error in one branch shouldn't kill the whole
                # tree; log and continue with the other branches' results.
                print(tactic_number, "-- branch error:", steps)
                continue
            if steps != [] :
                print(tactic_number, "-- finished(success)")
                return steps

    print(tactic_number, "-- finished(failure)")
    return []


def insert(tab, l, i) :
    if l >= len(tab) :
        tab.extend([[]] * (2*l+1 - len(tab)))
    tab[l].append(i)


length = [[]] #tactics grouped by solution length


for i in range(len(position)) :
    k = str(i)
    l = 0
    while next_tactic[k] != None :
        k = str(next_tactic[k])
        l += 1
    insert(length, l, i)


# ---------------------------------------------------------------------------
# Outer loop: bounded thread pool (per your sizing: outer_max_workers = 16),
# one Pytanque STDIO process per worker. Each worker drives its theorem's
# tree with its own asyncio event loop via asyncio.run(...).
#
# Two tiers of retry on a Pytanque timeout:
#   1. Inside PytanqueGuard._call, a timed-out call is retried up to
#      max_call_retries times on the SAME client/process (see PytanqueGuard
#      docstring above).
#   2. Only if all of those retries also time out does the guard become
#      poisoned. At that point this outer loop tears down the process and
#      retries the WHOLE theorem from scratch with a fresh Pytanque process,
#      up to max_retries_per_theorem times.
# ---------------------------------------------------------------------------
max_retries_per_theorem = 2

def worker(j) :
    if l[j] < len(examples) :
        return []

    attempt = 0
    while attempt <= max_retries_per_theorem :
        attempt += 1
        guard, cm = make_guarded_client(lambda: Pytanque(mode=PytanqueMode.STDIO))
        try :
            steps = asyncio.run(make_tree(guard, l[j]))
            if steps != [] or not guard.poisoned :
                return steps
            # guard.poisoned and steps == []: the attempt failed because of
            # a Pytanque timeout, not because the search legitimately ran
            # out of budget. Worth a retry with a fresh process.
            print(f"theorem {l[j]} -- retrying after poisoned client (attempt {attempt})")
        finally :
            guard.shutdown()
            try :
                cm.__exit__(None, None, None)
            except Exception :
                # process may already be in a bad state after a timeout;
                # don't let cleanup failure mask the real result.
                pass

    return []


for i in range(len(length)) :
    t_start = time.time()
    l = length[i]
    nb_tries = 0
    nb_solves = 0

    with ThreadPoolExecutor(max_workers=outer_max_workers) as pool:
        new_good_steps = list(pool.map(worker, range(len(l))))

    print(f"Score(difficulty = {i+1}) = {sum([steps != [] for steps in new_good_steps])}/{len(l) - nb_examples}")
    print("TIME : ", time.time() - t_start)
    good_proof_steps += new_good_steps

with open("output_treefinement.dump", 'wb') as f:
    pickle.dump(good_proof_steps, f)
