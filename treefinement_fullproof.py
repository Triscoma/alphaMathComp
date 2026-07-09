
'''
Contruit l'arbre de treefinement.
'''

import os
import json
import re
from queue import PriorityQueue
from pytanque import Pytanque, PytanqueMode
from openai import OpenAI, AsyncOpenAI
from concurrent.futures import ThreadPoolExecutor, TimeoutError
from threading import Lock
import time
import random
import asyncio
from pathlib import Path
import datetime
import copy

t_start = time.time()

date = datetime.datetime.now()
results_dir = Path("results") / f"{date.strftime("%c")}"
results_dir.mkdir(parents=True, exist_ok=True)

#parameters
arity = 1
beam_size = 4
iter_max = 1
nb_examples = 3
max_sample_size = 3

MAX_RANGE = 20 # pour ne pas itérer sur tout quand on veut juste tester, mettre à 10000 sinon

#alpha = 1
#beta = 1

def penalty(nb_error, depth, consecutive_errors) :
    return nb_error / depth

'''
def penalty(nb_error, depth, consecutive_errors) :
    return consecutive_errors
'''

#modèles de test : 
#model = "nvidia/nemotron-3-nano-30b-a3b:free"
#model = "nvidia/nemotron-3-nano-omni-30b-a3b-reasoning:free"

#model = "openai/gpt-4.1" # gros modèle
#model = "mistralai/mistral-small-2603"
#model = "mistralai/Mistral-7B-Instruct-v0.3"
#model = "deepseek/deepseek-v4-pro"
model = "deepseek/deepseek-v4-flash" # pas cher

prefix = 'data/output/eval_tmp/'

with open(prefix + 'filepath.json') as filepath_json :
    filepath = json.load(filepath_json)

with open(prefix + 'position.json') as position_json :
    position = json.load(position_json)

with open(prefix + 'tactic.json') as tactic_json :
    tactic = json.load(tactic_json)

with open(prefix + 'next_tactic.json') as next_tactic_json :
    next_tactic = json.load(next_tactic_json)

with open(prefix + 'statement.json') as statement_json :
    statement = json.load(statement_json)

with open(prefix + 'theorem.json') as theorem_json :
    theorem = json.load(theorem_json)

with open('data/output.json') as output_json : 
    data = json.load(output_json)

with open('confidential.json') as confidential_json :
    confidential = json.load(confidential_json)
    API_KEY = confidential["API_KEY"]

chatbot = OpenAI(
        base_url="https://openrouter.ai/api/v1",
        api_key=API_KEY,
    )

'''
chatbot = OpenAI(
    base_url="http://127.0.0.1:6379/v1",
    api_key="EMPTY",
)
'''

def parse_fullproof(text, i) :
    #print("PARSE_INPUT : ", text)
    ans = []
    buffer = ""
    while i < len(text) - 4 :
        if text[i:i+4] == 'Qed.' :
            i += 4
            break
        buffer += text[i]
        if text[i] == '.' :
            buffer = buffer.strip()
            if len(buffer) <= 1 :
                i += 1
                continue
            elif buffer[len(buffer) - 1] != '.':
                buffer += '.'
            ans.append(buffer)
            buffer = ""
        i += 1
    ans.append("Qed.")
    return (ans, i)

def parse_proposals(text) :
    proofs = []
    i = 0
    while i < len(text) - 6 :
        if text[i:i+6] == 'Proof.' :
            proof, i = parse_fullproof(text, i+6)
            proofs.append(["Proof."] + proof)
        else :
            i += 1
    return proofs

examples = []
seen_lemmas = set()
def init_examples() :
    pos = 0
    while len(seen_lemmas) <= nb_examples :
        tactic_number = str(pos)
        pos += 1
        lemma = theorem[tactic_number]
        if lemma in seen_lemmas :
            continue
        seen_lemmas.add(lemma)
        examples.append({"theorem" : theorem[tactic_number], "goal" : statement[tactic_number], "proof corrected" : data[theorem[tactic_number]]["proof"], "errors" : [], "proof tried" : None})

init_examples()

good_proof_steps = examples

# renvoie une tactique générée par llm, ainsi que la proof_state et l'éventuelle erreur qui survient
def ask_llm(client, client_lock, tactic_number, prev_tactic, proof_st, errors, feedback) :

    with client_lock :
        try :
            goals = client.goals(proof_st)
        except Exception as err :
            return [["Qed."]]

    prompt = "You have the following goals in your current context in coq (mathematical components): \n\n"
    for g in goals : 
        prompt += g.pp
    prompt += "\n\nFinish the proof.\n"
    prompt += "Your proof should start by 'Proof.' and end by 'Qed.' \n"
    prompt += "Write each tactic of your proof on a separate line, in particular each line should end by a point.\n"
    prompt += f"Propose {arity} options.\n"
    prompt += "Don't write anything else, and don't annotate your answer."

    prompt += "\n\nTo help you, here are some examples of proofs in mathcomp for a given goal statement:\n"
    for ex in random.sample(good_proof_steps, min(max_sample_size, len(good_proof_steps))):
        prompt += "\nGoal : \n" + ex["goal"] + "\n\n"
        if (ex["errors"] == []) :
            prompt += "\nProof : " + ex["proof corrected"] + "\n"
        else :
            prompt += "\nUnsuccessful attempt : " + ex["proof tried"]
            prompt += "\nError : " + ex["error"]
            prompt += "\nProof corrected : " + ex["proof corrected"] + "\n"



    if prev_tactic != None :
        prompt += "\nThe last proof you tried is :\n" + '\n'.join(prev_tactic)
    if (errors != []) :
        prompt += "\nbut got the errors : \n" + '\n'.join(errors) + "\n"
    if feedback :
        print("feedback : ", feedback)
        prompt += "\nAnd you got the following feedback (may have been truncated if longer than 50 lines) :\n"
        for level, message in feedback:
            prompt += f"Level {level}: {message}\n"
    #print("\nPROMPT : ", prompt)


    try :
        response = chatbot.responses.create(
            model=model,
            input=prompt,
            extra_body={
                "reasoning" : {
                    "effort" : "high",
                    "exclude" : True
                }
            },
        )
        print("ANSWER : ", response.output_text)
        proofs = parse_proposals(response.output_text)

        #proofs = parse_proposals(input())
    except Exception as err:
        print("Error while querying llm : ", err)
        proofs = ["Qed."]
    return proofs


def make_tree(client, tactic_number_, client_lock) :
    print("tactic_number : ", tactic_number_)
    tactic_number = str(tactic_number_)
    tree = [[]]
    parent = [0]
    proof_tried = [None]
    errors = [[]]
    depth = [0]
    nb_err = [0]
    nb_cons_err = [0]
    node_feedback = [[]]

    file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
    line, char = pos["line"], pos["character"]


    with client_lock :
        proof_state = client.get_state_at_pos(file, line, char)

    it_lock = Lock()
    #goals_seen = set()


    pq = PriorityQueue() # pairs of (penalty, node_id)
    pq.put((0, 0))


    def make_new_branches(node) : 
        ''' Generate arity children to node and returns generated steps if one tactic succeeded'''
        nonlocal tactic_number
        proofs = ask_llm(client, client_lock, tactic_number, proof_tried[node], proof_state, errors[node], node_feedback[node])
        print("PROOFS:", proofs)
        for proof in proofs :
            new_feedback = []
            proof_st = copy.deepcopy(proof_state)
            proof_errors = []
            for tac in proof :
                try :
                    with client_lock :
                        proof_st = client.run(proof_st, "Timeout 10 " + tac)
                        print("Typeckeck")
                        new_feedback += proof_st.feedback[:50]
                        new_feedback = new_feedback[:50]
                except Exception as err :
                    print("did not typecheck, ERROR : ", tac + " : " + str(err))
                    proof_errors.append(tac + " : " + str(err))

            with it_lock :
                new_node = len(parent)
                tree.append([])
                tree[node].append(new_node)
                parent.append(node)
                proof_tried.append(proof)
                errors.append(proof_errors)
                depth.append(depth[node] + 1)
                node_feedback.append(new_feedback)
                if proof_st.proof_finished :
                    print("end new_branch (solution found, extracting...)")
                    # Retrieve the correction steps
                    #print("parent : ", parent)
                    #print("tree : ", tree)
                    #print("Recuperation de l'arbre...")
                    steps = []
                    n = new_node
                    n_ = n
                    while n_ != 0 :
                        n_ = parent[n_]
                        goals = []
                        with client_lock :
                            for g in client.goals(proof_state):
                                goals.append(g.pp)
                        steps.append({"theorem" : theorem[tactic_number], "goal" : goals, "tactic tried" : proof_tried[n_], "errors" : errors[n_], "tactic corrected" : proof_tried[n]})
                    return steps
                else :
                    # la preuve n'est pas finie, donc il faudra explorer ce noeud plus tard
                    pq.put((len(proof_errors), new_node))
                    #with client_lock :
                    #    goals_seen.add(client.goals(proof_state[new_node])[0].pp)

        print("end new_branch (nothing)")
        return []

    iter_rem = iter_max
    while iter_rem :
        #print("it = ", it)
        beam_nodes = []
        for _ in range(beam_size) :
            if pq.empty() :
                break
            pen, node = pq.get()
            beam_nodes.append(node)
        iter_rem -= len(beam_nodes)

        def make_beam(it_beam) :
            return make_new_branches(beam_nodes[it_beam]) 

        with ThreadPoolExecutor() as pool:
            for steps in list(pool.map(make_beam, range(len(beam_nodes)))) :
                if steps != [] :
                    return steps


    return []



nb_try = [0 for i in range(42)]    
nb_success = [0 for i in range(42)]

tactics = []
N = min(MAX_RANGE, len(position))
for i in range(N) :
    k = str(i)
    if (theorem[k] in seen_lemmas):
        continue
    l = 0
    while next_tactic[k] != None :
        k = str(next_tactic[k])
        l += 1
    tactics.append((l, i))

tactics.sort()
print("tactics : ", tactics)

steps_lock = Lock()
def worker(j) :
    global nb_try, nb_success, good_proof_steps
    l, i = tactics[j]
    with Pytanque(mode=PytanqueMode.STDIO) as client :
        client_lock = Lock()
        new_good_steps = make_tree(client, i, client_lock)
    with steps_lock :
        nb_try[l] += 1
        if new_good_steps != [] :
            nb_success[l] += 1
            print(i, f"[difficulty = {l+1}] -- finished(success) --> {nb_success[l]}/{nb_try[l]}")
        else :
            print(i, f"[difficulty = {l+1}] -- finished(failure) --> {nb_success[l]}/{nb_try[l]}")
        good_proof_steps += new_good_steps

with ThreadPoolExecutor(max_workers=1) as pool: #max_workers=... pour choisir le nb max de threads
    list(pool.map(worker, range(len(tactics))))

for l in range(42):
        print(f"Score(difficulty = {l+1}) = {nb_success[l]}/{nb_try[l]}")


p = results_dir / "final_results.json"
final_results = {
        "nb_try": nb_try,
        "nb_success": nb_success,
        "total_score" : sum(nb_success)/sum(nb_try),
        "exec_time" : time.time() - t_start,
    }
with open(p, "w") as f: 
    json.dump(final_results, f, indent=2)
    print(f"Score Total : {sum(nb_success)}/{sum(nb_try)}")
    print("TIME : ", time.time() - t_start)

#with open("output_treefinement.dump", 'wb') as f:
#    pickle.dump(good_proof_steps, f)
