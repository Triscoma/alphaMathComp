### Dependencies :
  - python >= 3.12
  - coq 8.20.0
  - coqlsp 0.2.3+9.0
  - (for the given mathcomp examples) : mathcomp 2.4.0

### Use : 
  - Make data files with goal2tac (data/output.json with dataset/format_project.py then data/output/train_tmp and data/output/eval_tmp with dataset/create.py)
  - Chose the suitable model and parameters in the source of treefinement.py (or treefinement_fullproof.py)
  - If you want to run the model on OpenRouter :
    - Make a json confidential.json containing your api key in the field "API_KEY".
  - Else :
    - In treefinement.py, change the chatbot parameters to make it run the way you want
  - Run the script with python3 -m treefinement (or python3 -m treefinement_fullproof)
