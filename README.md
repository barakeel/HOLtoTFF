Installation (on Linux) (need emacs installed with HOL interactive mode)

First step: Installing (polyml/HOL)
- look for the latest version of polyml (http://www.polyml.org/)
- extract and type ./configure --enable-shared instead of ./configure
- go to the directory you want to install HOL
- type git clone https://github.com/mn200/HOL
- type cd HOL 
- type poly < tools/smart-configure.sml
- type bin/build (go and drink a coffee, this process may take a while)

Second step: Add the HOL path to your bash.rc directory 
- open .bashrc with a text editor (.bashrc is an hidden file in your home directory)
- add at the end of the file PATH=$PATH:$HOME/HOL/bin 
  (here you should replace $HOME by the location of your HOL directory if it's not in $HOME) 
- save the file

Third step: Installing HOLtoTFF
- open a terminal 
- go to the directory you want to install HOLtoTFF
- type git clone https://github.com/barakeel/HOLtoTFF
- type cd HOLtoTFF
- open beagle.sml and change the directory path (e.g. val directory = yourHOLtoTFFpath)
- type Holmake in the termianal

Fourth step: Testing
- open test.sml with emacs 
- split the window 
- run hol interactive mode (M-h h)
- select any instruction and then (M-h M-r) to execute it
- open any libraries you want to test 

  
