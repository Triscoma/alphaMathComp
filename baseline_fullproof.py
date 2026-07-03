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

nb_examples = 5

max_sample_size = 50

#model = "openai/gpt-4.1" # gros modèle
#model = "mistralai/mistral-small-2603"
#model = "nvidia/nemotron-3-nano-30b-a3b:free" # modèle de test
#model = "mistralai/Mistral-7B-Instruct-v0.3"
model = "deepseek/deepseek-v4-pro"


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


def parse_fullproof(text) :
    #print("PARSE_INPUT : ", text)
    ans = []
    buffer = ""
    for i in range(len(text)) :
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
        examples.append({"statement" : statement[tactic_number], "proof" : data[theorem[tactic_number]]["proof"]})

init_examples()

good_proof_steps = examples

# renvoie une tactique générée par llm, ainsi que la proof_state et l'éventuelle erreur qui survient
def ask_llm(client, client_lock, proof_st) :

    with client_lock :
        goal = client.goals(proof_st)[0].pp

    prompt = "Here is a goal statement in coq (mathematical components): \n\n"
    prompt += goal
    prompt += "\n\nProve it.\n"
    prompt += "Write each tactic of your proof on a separate line, in particular each line should end by a point.\n"

    prompt += "\n\nTo help you, here are some examples of proofs in mathcomp for a given goal statement:\n"
    for ex in random.sample(good_proof_steps, min(max_sample_size, len(good_proof_steps))):
        prompt += "\nGoal : \n" + ex["statement"] + "\n\n" + "Proof :" + ex["proof"] + "\n\n"
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
        answer = response.output_text
        print("ANSWER : ", answer)
        tacs = parse_fullproof(answer)
    except Exception as err:
        print("Error while querying llm : ", err)
        tacs = ["idtac."]
    return tacs

def try_solving(client, tactic_number_, client_lock) :
    print("tactic_number : ", tactic_number_)
    tactic_number = str(tactic_number_)

    file, pos = "./rocq/" + filepath[tactic_number], position[tactic_number]
    line, char = pos["line"], pos["character"]
    with client_lock :
        proof_state = client.get_state_at_pos(file, line, char)

    tacs = ask_llm(client, client_lock, proof_state)
    print("TACS :", tacs)
    for tac in tacs :
        try :
            with client_lock :
                proof_state = client.run(proof_state, "Timeout 10 " + tac)
            print("typechecked")
        except Exception as err :
            print("DID'NT typechecked")
            continue

        if proof_state.proof_finished :
            return True
    return False

steps_lock = Lock()

tactics = []
nb_try = [0 for i in range(42)]    
nb_success = [0 for i in range(42)]

t_start = time.time()
for i in range(len(position)) : 
    k = str(i)
    if (theorem[k] in seen_lemmas):
        continue
    seen_lemmas.add(theorem[k])
    l = 0
    while next_tactic[k] != None :
        k = str(next_tactic[k])
        l += 1
    tactics.append((l, i))


with Pytanque(mode=PytanqueMode.STDIO) as client :
    client_lock = Lock()
    def worker(j) :
        global nb_try, nb_success
        l, i = tactics[j]
        is_solved = try_solving(client, i, client_lock)
        with steps_lock :
            nb_try[l] += 1
            if is_solved :
                nb_success[l] += 1
                print(i, f"[difficulty = {l+1}] -- finished(success) --> {nb_success[l]}/{nb_try[l]}")
            else :
                print(i, f"[difficulty = {l+1}] -- finished(failure) --> {nb_success[l]}/{nb_try[l]}")

    with ThreadPoolExecutor() as pool: #max_workers=... pour choisir le nb max de threads
        list(pool.map(worker, range(len(tactics))))

for l in range(42):
    print(f"Score(difficulty = {l+1}) = {nb_success[l]}/{nb_try[l]}")
print(f"Score Total : sum(nb_success)/sum(nb_try)")
print("TIME : ", time.time() - t_start)
