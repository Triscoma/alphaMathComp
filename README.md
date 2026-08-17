# AlphaMathComp

## An automated step-prover for Rocq and MathComp that uses past errors to refine its answers. 
This is a proposal to adapt AlphaVerus' Treefinement method to this framework

### Dependencies :
  - python >= 3.12
  - coq 8.20.0
  - coqlsp 0.2.3+9.0
  - (for the given mathcomp examples) : mathcomp 2.4.0

### Usage : 
  - (only if you want to use a dataset other than ours) Make data files from the rocq files of your dataset with goal2tac (data/output.json with dataset/format_project.py then data/output/train_tmp and data/output/eval_tmp with dataset/create.py)
  - If you want to run the model on OpenRouter :
    - Make a json confidential.json containing your api key in the field "API_KEY".
  - Else :
    - In treefinement.py, change the chatbot parameters to make it run the way you want
  - Choose the desired model and parameters in the source of treefinement.py (or treefinement_fullproof.py)
    	- Main parameters are :
  		  - arity (number of leaves created when exploring a node)
        - iter_max (number of explored nodes)
        - nb_examples (number of examples used to make the initial dataset)
        - max_sample_size (maximum number of examples sampled from the previous good steps and corrections made by the program at each iteration)
  - Run the script with python3 -m treefinement (or python3 -m treefinement_fullproof)
