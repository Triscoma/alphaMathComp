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

date = datetime.datetime.now()
results_dir = Path("results") / f"{date.strftime("%c")}"
results_dir.mkdir(parents=True, exist_ok=True)

#parameters
arity = 3
beam_size = 4
iter_max = 12
nb_examples = 5
max_sample_size = 20

MAX_RANGE = 1000000 # pour ne pas itérer sur tout quand on veut juste tester

#alpha = 1
#beta = 1

def penalty(nb_error, depth, consecutive_errors) :
    return nb_error / depth

'''
def penalty(nb_error, depth, consecutive_errors) :
    return consecutive_errors
'''

#modèles de test : 
model = "nvidia/nemotron-3-nano-30b-a3b:free"
#model = "nvidia/nemotron-3-nano-omni-30b-a3b-reasoning:free"

#model = "openai/gpt-4.1" # gros modèle
#model = "mistralai/mistral-small-2603"
#model = "mistralai/Mistral-7B-Instruct-v0.3"
#model = "deepseek/deepseek-v4-pro"
#model = "deepseek/deepseek-v4-flash" # pas cher

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

def parse_tactics(text) :
    #print("PARSE_INPUT : ", text)
    ans = []
    buffer = ""
    for i in range(len(text)) :
        if (len(ans) == arity):
            break
        buffer += text[i]
        if text[i] == '.' or text[i] == '\n':
            buffer = buffer.strip()
            if len(buffer) <= 1 :
                continue
            elif buffer[len(buffer) - 1] != '.':
                buffer += '.'
            ans.append(buffer)
            buffer = ""
    if not ans :
        ans.append("idtac.")
    return ans


examples = []
example_lemmas = set()
def init_examples(client) :
    while len(example_lemmas) <= nb_examples :
        tactic_number = str(len(examples))
        lemma = theorem[tactic_number]
        example_lemmas.add(lemma)
        file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
        line, char = pos["line"], pos["character"]
        goal = client.goals(client.get_state_at_pos(file, line, char))[0].pp
        examples.append({"theorem" : tactic_number, "goal" : goal, "tactic tried" : None, "error" : None, "tactic corrected" : tactic[tactic_number]})

with Pytanque(mode=PytanqueMode.STDIO) as client:
    init_examples(client)

good_proof_steps = examples

# renvoie une tactique générée par llm, ainsi que la proof_state et l'éventuelle erreur qui survient
def ask_llm(client, client_lock, tactic_number, prev_tactic, proof_st, error, feedback) :

    with client_lock :
        goal = client.goals(proof_st)[0].pp

    prompt = "Here is a goal in coq (mathematical components): \n\n"
    prompt += goal
    prompt += "\n\nWrite the next command you would use to solve it.\n"
    prompt += f"Propose up to {arity} options.\n"
    prompt += "Don't write anything else, and don't annotate your answer. Write eache proposal on a new line."
    prompt += "Each of your proposal should end by a point.\n"

    prompt += "\n\nTo help you, here are some examples of proof steps in mathcomp for a given goal statement:\n"
    filtered_steps = [step for step in good_proof_steps if step["theorem"] != tactic_number]
    for ex in random.sample(filtered_steps, min(max_sample_size, len(filtered_steps))):
        prompt += "\nGoal : \n" + ex["goal"] + "\n"
        if (ex["error"] is None) :
            prompt += "\nNext tactic : " + ex["tactic corrected"] + "\n"
        else :
            prompt += "\nUnsuccessful tactic : " + ex["tactic tried"]
            prompt += "\nError : " + ex["error"]
            prompt += "\nTactic corrected : " + ex["tactic corrected"] + "\n"
    #prompt += "\nAnd some examples of good proof steps:\n" + str(current_good_steps)
    if prev_tactic != None :
        prompt += "\nThe last command you tried is :\n" + prev_tactic
    if (error != None) :
        prompt += "\nbut got the error : \n" + error + "\nCorrect your answer.\n"

    prompt += "\nSo far, you got the following feedback (may have been truncated if longer than 50 lines) :\n"
    for level, message in feedback:
        prompt += f"Level {level}: {message}\n"
    prompt += "\nYou can use commands like 'Check', 'Search', etc. if you need more information about the context.\n"
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
        #print("ANSWER : ", response.output_text)
        tacs = parse_tactics(response.output_text)
    except Exception as err:
        print("Error while querying llm : ", err)
        tacs = ["idtac."]
    return tacs




def make_tree(client, tactic_number_, client_lock) :
    print("tactic_number : ", tactic_number_)
    tactic_number = str(tactic_number_)
    tree = [[]]
    parent = [0]
    proof_state = []
    tactic_tried = [None]
    error = [None]
    depth = [0]
    nb_err = [0]
    nb_cons_err = [0]
    node_feedback = [[]]

    file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
    line, char = pos["line"], pos["character"]
    with client_lock :
        proof_state.append(client.get_state_at_pos(file, line, char))

    it_lock = Lock()
    #goals_seen = set()


    pq = PriorityQueue() # couples of (penalty, node_id)
    pq.put((0, 0))


    def make_new_branches(node) : 
        ''' Generate arity children to node and returns generated steps if one tactic succeeded'''
        nonlocal tactic_number
        #tac, new_state, new_error, new_feedback = ask_llm(tactic_tried[node], proof_state[node], error[node], previous_lemmas, node_feedback[node])
        proof_st = proof_state[node]
        new_feedback = node_feedback[node][:40] + proof_st.feedback[:50] #If there was an error, the last feedback is contained in the current proof state. I don't know how to fix it, it's not a major issue anyway
        tacs = ask_llm(client, client_lock, tactic_number, tactic_tried[node], proof_st, error[node], new_feedback)
        #print("TACS :", tacs)
        for tac in tacs :
            try :
                with client_lock :
                    new_state = client.run(proof_st, "Timeout 10 " + tac)
                    new_error = None
            except Exception as err :
                #print("\nERROR : ", str(err))
                new_state = proof_st
                new_error = str(err)

            with it_lock :
                new_node = len(parent)
                tree.append([])
                tree[node].append(new_node)
                parent.append(node)
                proof_state.append(new_state)
                tactic_tried.append(tac)
                error.append(new_error)
                depth.append(depth[node] + 1)
                nb_err.append(nb_err[node] + 0 if error[new_node] is None else 1)
                nb_cons_err.append(0 if error[new_node] is None else 1 + nb_cons_err[node])
                node_feedback.append(new_feedback)
                if proof_state[new_node].proof_finished :
                    # Retrieve the correction steps
                    #print("parent : ", parent)
                    #print("tree : ", tree)
                    #print("Recuperation de l'arbre...")
                    steps = []
                    n = new_node
                    while n != 0 :
                        n_ = parent[n]
                        while error[n_] != None :
                            n_ = parent[n_]
                        def dfs(u) :

                            with client_lock :
                                goal = client.goals(proof_state[u])[0].pp
                            steps.append({"theorem" : theorem[tactic_number], "goal" : goal, "tactic tried" : tactic_tried[u], "error" : error[u], "tactic corrected" : tactic_tried[n]})

                            for v in tree[u] :
                                if (error[v] != None) :
                                    dfs(v)
                        dfs(n_)
                        n = n_
                    return steps
                else :
                    # la preuve n'est pas finie, donc il faudra explorer ce noeud plus tard
                    pq.put((penalty(nb_err[new_node], depth[new_node], nb_cons_err[new_node]), new_node))
                    #with client_lock :
                    #    goals_seen.add(client.goals(proof_state[new_node])[0].pp)

        return []


    for it in range(int(iter_max / beam_size)) :
        #print("it = ", it)
        beam_nodes = []
        for _ in range(beam_size) :
            if pq.empty() :
                break
            pen, node = pq.get()
            beam_nodes.append(node)

        def make_beam(it_beam) :
            return make_new_branches(beam_nodes[it_beam]) 

        with ThreadPoolExecutor() as pool:
            for steps in list(pool.map(make_beam, range(len(beam_nodes)))) :
                if steps != [] :
                    with it_lock :
                        Tree = {
                            "tree" : tree,
                            "parent" : parent,
                            "proof_state" : [x.to_json() for x in proof_state],
                            "tactic_tried" : tactic_tried,
                            "error" : error,
                            "depth" : depth,
                            "nb_err" : nb_err,
                            "nb_const_err" : nb_cons_err,
                            "node_feedback" : node_feedback,
                        }
                        p = results_dir / f"tactic_{tactic_number_}.json"
                        with open(p, "w") as f: 
                            json.dump(Tree, f, indent=2)
                    return steps


    with it_lock :
        Tree = {
            "tree" : tree,
            "parent" : parent,
            "proof_state" : [x.to_json() for x in proof_state],
            "tactic_tried" : tactic_tried,
            "error" : error,
            "depth" : depth,
            "nb_err" : nb_err,
            "nb_const_err" : nb_cons_err,
            "node_feedback" : node_feedback,
        }
        p = results_dir / f"tactic_{tactic_number_}.json"
        with open(p, "w") as f: 
            json.dump(Tree, f, indent=2)

    return []



nb_try = [0 for i in range(42)]    
nb_success = [0 for i in range(42)]

tactics = []
for i in range(len(position)) :
    k = str(i)
    if (theorem[k] in example_lemmas):
        continue
    l = 0
    while next_tactic[k] != None :
        k = str(next_tactic[k])
        l += 1
    tactics.append((l, i))

tactics.sort()

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

with ThreadPoolExecutor() as pool: #max_workers=... pour choisir le nb max de threads
    list(pool.map(worker, range(len(tactics))))

for l in range(42):
        print(f"Score(difficulty = {l+1}) = {nb_success[l]}/{nb_try[l]}")
print(f"Score Total : sum(nb_success)/sum(nb_try)")
print("TIME : ", time.time() - t_start)

#with open("output_treefinement.dump", 'wb') as f:
#    pickle.dump(good_proof_steps, f)
