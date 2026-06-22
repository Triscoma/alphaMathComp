'''
contruit l'arbre de treefinement.
'''

import os
import json
import pickle
import re
from queue import priorityqueue
from pytanque import pytanque, pytanquemode
from openai import openai, asyncopenai
from concurrent.futures import threadpoolexecutor, timeouterror
from threading import lock
import time
import random
import asyncio

#parameters
arity = 2
iter_max = 32
nb_examples = 5

max_sample_size = 50
#max_waiting = 20 #for client.goals issues
max_range = 20 # pour ne pas itérer sur tout quand on veut juste tester

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
    api_key = confidential["api_key"]



chatbot = openai(
        base_url="https://openrouter.ai/api/v1",
        api_key=api_key,
    )

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
        examples.append({"goal" : goal, "tactic tried" : none, "error" : none, "tactic corrected" : tactic[tactic_number]})

with Pytanque(mode=PytanqueMode.STDIO) as client :
    init_examples(client)

good_proof_steps = examples

# renvoie une tactique générée par llm, ainsi que la proof_state et l'éventuelle erreur qui survient
def ask_llm(client, prev_tactic, proof_st, error, feedback) :
    #print("ask_llm\n")
    #todo : corriger bugs : client.goals bloque souvent pour essentiellement 2 raisons : indexoutofbounds / boucle indéfiniment
    # --> vient peut-être des tactiques vides

    goal = client.goals(proof_st)[0].pp

    prompt = "here is a goal in coq (mathematical components): \n\n"
    prompt += goal
    prompt += "\n\nwrite the next command you would use to solve it.\n"
    prompt += f"propose up to {arity} options.\n"
    prompt += "don't write anything else, and don't annotate your answer. write eache proposal on a new line."
    prompt += "each of your proposal should end by a point.\n"

    prompt += "\n\nto help you, here are some examples of proof steps in mathcomp for a given goal statement:\n"
    for ex in random.sample(good_proof_steps, max(5, min(max_sample_size, len(good_proof_steps)))):
        prompt += "\ngoal : \n" + ex["goal"] + "\n"
        if (ex["error"] is none) :
            prompt += "\nnext tactic : " + ex["tactic corrected"] + "\n"
        else :
            prompt += "\nunsuccessful tactic : " + ex["tactic tried"]
            prompt += "\nerror : " + ex["error"]
            prompt += "\ntactic corrected : " + ex["tactic corrected"] + "\n"
    #prompt += "\nand some examples of good proof steps:\n" + str(current_good_steps)
    if prev_tactic != none :
        prompt += "\nthe last command you tried is :\n" + prev_tactic
    if (error != none) :
        prompt += "\nbut got the error : \n" + error + "\ncorrect your answer.\n"

    prompt += "\nso far, you got the following feedback (may have been truncated if longer than 50 lines) :\n"
    for level, message in feedback:
        prompt += f"level {level}: {message}\n"
    prompt += "\nyou can use commands like 'check', 'search', etc. if you need more information about the context.\n"
    #print("\nprompt : ", prompt)


    try :
        response = chatbot.responses.create(
                model=model,
                input=prompt
                )
        #print("answer : ", response.output_text)
        tacs = parse_tactics(response.output_text)
    except exception as err:
        print("error while querying llm : ", err)
        tacs = ["idtac."]
    return tacs




def make_tree(client, tactic_number_) :
    print("tactic_number : ", tactic_number_)
    tactic_number = str(tactic_number_)
    tree = [[]]
    parent = [0]
    depth = [0]
    proof_state = []
    tactic_tried = [none]
    error = [none]
    node_feedback = [[]]

    file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
    line, char = pos["line"], pos["character"]
    proof_state.append(client.get_state_at_pos(file, line, char))

    #goals_seen = set()


    pq = priorityqueue() # couples of (penalty, node_id)
    pq.put((0, 0))


    def make_new_branches(pen, node) : 
        ''' generate arity children to node and returns generated steps if one tactic succeeded'''
        #tac, new_state, new_error, new_feedback = ask_llm(tactic_tried[node], proof_state[node], error[node], previous_lemmas, node_feedback[node])
        proof_st = proof_state[node]
        new_feedback = node_feedback[node][:40] + proof_st.feedback[:50] #if there was an error, the last feedback is contained in the current proof state. i don't know how to fix it, it's not a major issue anyway
        tacs = ask_llm(client, tactic_tried[node], proof_st, error[node], new_feedback)
        print("tacs :", tacs)
        for tac in tacs :
            try :
                new_state = client.run(proof_st, tac)
                new_error = none
            except exception as err :
                #print("\nerror : ", str(err))
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
                # retrieve the correction steps
                #print("parent : ", parent)
                #print("tree : ", tree)
                #print("recuperation de l'arbre...")
                steps = []
                n = new_node
                while n != 0 :
                    n_ = parent[n]
                    while error[n_] != none :
                        n_ = parent[n_]
                    def dfs(u) :
                        goal = client.goals(proof_state[u])[0].pp
                        steps.append({"goal" : goal, "tactic tried" : tactic_tried[u], "error" : error[u], "tactic corrected" : tactic_tried[n]})
                        for v in tree[u] :
                            if (error[v] != none) :
                                dfs(v)
                    dfs(n_)
                    n = n_
                return steps
            else :
                # la preuve n'est pas finie, donc il faudra explorer ce noeud plus tard
                pq.put((pen + (0 if error[new_node] is none else 1), new_node))
        return []


    for it in range(iter_max) :
        #print("it = ", it)
        pen, node = pq.get()
        steps = make_new_branches(pen, node)
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
    if (theorem[k] in example_lemmas):
        continue
    l = 0
    while next_tactic[k] != none :
        k = str(next_tactic[k])
        l += 1
    insert(length, l, i)

with Pytanque(mode=PytanqueMode.STDIO) as client :
    for i in range(len(length)) : 
        t_start = time.time()
        l = length[i]
        nb_tries = 0
        nb_success = 0
        nb_trees = min(len(l), max_range)


        def worker(j) :
            return make_tree(client, l[j])

        new_good_steps = []
        for j in range(nb_trees):
            new_good_steps += worker(j)
        if new_good_steps != []:
            nb_success += 1
        nb_tries += 1
        print("new_good_steps : \n", new_good_steps)

        print(f"score(difficulty = {i+1}) = {nb_success}/{nb_tries}")
        print("time : ", time.time() - t_start)
        good_proof_steps += new_good_steps

with open("output_treefinement.dump", 'wb') as f:
    pickle.dump(new_good_steps, f)

