Installation (on Linux) (need emacs installed)

First step: Installing (polyml/HOL)
- open a terminal
- type sudo apt-get install polyml
- open a terminal 
- go to the directory you want to install HOL
- type git clone https://github.com/mn200/HOL
- type cd HOL 
- type poly < tools/smart-configure.sml
- type bin/build (go and drink a coffee (this process may take a while))

Second step: Add the HOL path to your bash.rc directory 
- open .bashrc with a text editor
  (.bashrc is an hidden file in your home directory)
- add at the end of the file PATH=$PATH:$HOME/HOL/bin 
  (here you should replace $HOME by the location of your HOL directory) 
- save the file

Third step: Installing HOLtoTFF
- open a terminal 
- go to the directory you want to install HOLtoTFF
- type git clone https://github.com/barakeel
- type cd HOLtoTFF
- type Holmake
- open test.sml with emacs 
- split the window 
- run hol interactive mode (M-h h)
- select any instruction and then (M-h M-r) to execute it
- open any libraries you want to test
    (main is enough to test the examples)
 - result are shown as text files in HOLtoTFF/result
   (if beagle is not install it will show you only the translation to tff in
    result/filename_hol and result/filename_tff) 
 
 Fourth step : installing beagle 
 -
 
 Fifth step : modifying the shell script to call beagle from HOL