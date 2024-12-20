### Formal Verification Overview:
***Note: As of 18 Dec 2024 Jasper is only installed on the main ECE Linux server, not C2S2's. You can log in with ssh -X NETID@ecelinux.ece.cornell.edu.***

Formal verification offers extensive coverage with minimal effort by enabling the proof of assertions across sets of states rather than testing each individually. This process involves mathematically demonstrating that certain properties hold true for any possible state in the design under test (DUT), while also validating the reachability of specific states. Given the potential size of the state space, we can apply assumptions—such as starting with reset high—to narrow the space. To ensure the quality of our tests, tools like Jasper can provide coverage data, revealing how many possible states and signals have been tested. This allows us to prove the correctness of properties based on the specified assumptions with absolute certainty.

### Setting Up Jasper
<!-- <IMAGE> -->

Jasper is a Cadence software designed to facilitate formal verification as well as other verification techniques. It is a GUI application which is installed on the ECE Linux server.

##### X Forwarding
Jasper is a GUI application, so using it on the server requires X forwarding to be set up on your local machine. Instructions vary by OS and are easily available on the internet, but this normally entails downloading an X server, like vcxsrv for Windows, and using ssh -X instead of just ssh. Alternative, if you use VSCode, follow this TODO. 

##### Path and module loading
*Note, this should already be done via the `setup-c2s2.sh`. However, this will be included here incase that changes in the future* <br>

In order to run Jasper, you should first add the binary to your path. Then, you need to load the `cadence` module.
```
export PATH=/opt/cadence/jasper_2024.09/bin:$PATH
source ~/.bashrc
module load cadence
```
<br>
To ensure everything works, run:

```
which jaspergold
```

### The Jasper Environment
Once all the appropriate setup has been done, navigate to your testing directory. You can open Jasper with: 
```
jg
```
Jasper will try to create a file in your working directory, and it will fail to run in a read-only directory.

The Jasper GUI has three main sections:
1. **Design Hierarchy**:  
   The Design Hierarchy tab shows all the modules in your design.

2. **Property Table**:  
   The Property Table shows all the properties in your design and their corresponding verification statuses.

3. **Console**:  
   The Console displays logs, messages, and any output from the verification process.

#### Properties, sequences, assertions, covers
##### *Properties*
A property combines sequences and boolean expressions to specify a design behavior that should hold true. They define what should be true about the design's behavior under certain conditions. As an example, considered the property *p* defined below:
```
property p;

  @(posedge clk) req |-> ##1 gnt;

endproperty
```
This property asks to check whether if `req` being true on one clock positive edge means `gnt` will be true 1 cycle later.

##### *Sequences*
A sequence defines a series of events or conditions over time. Sequences are fundamental in describing temporal behaviors in hardware designs. They are constructed using boolean expressions and temporal operators. Consider the following example: 

```
sequence seq;
  $rose(a) ##[1:8] $rose(b);
endsequence
```
In the above example, the sequence `seq` describes a rising and b rising between 1 and 8 cycles later, inclusive. You cannot directly assert sequences; they must be inside properties. 
```
property p;
  @(posedge clk) seq;
endproperty
```

*Note: $rose(signal) is a shorthand that evaluates to signal && !signal[1], indicating that signal is high in the current cycle but was low in the previous cycle.*

##### *Assertions*
Assertions are used to check that a property holds true during simulation. The verification engine does so by checking whether the property is ever false under the given conditions or stimulus. Consider the following example: 
```
assert property (@(posedge clk) disable iff (rst) req |-> ##1 gnt);
```
This example asserts whenever `req` is true on one clock positive edge, `gnt` will be true 1 cycle later. The assertion is also disabled when `rst` is active, which is particularly useful. Assertions can be named for easier organization: 

```
STATE_A : assert property( STATE_A_PROP );
```
If a property is false, Jasper will return a counterexample trace, showing where this assertion fails. This can be accessed by double-clicking the failing assertion in the Property Table. If the assertion does not fail, no trace is returned, because the assertion is true for every possible model state. 

###### *Covers*
Cover statements are used to monitor whether certain conditions or sequences occur during simulation, aiding in coverage analysis. Consider the following cover: 

```
cover property (p); 
```
This cover checks whether the property *p* is ever true during simulation. Covers can utilize the same kinds of properties as assertions, but the engine only tries to prove it is true for some model state. You can cover a property like this:
```
STATE_A : cover property( STATE_A_PROP );
```
If a property is covered, the engine will return an example case in which the property is true which can be accessed by double-clicking the passing cover in the Property table. If the cover fails, no such case exists.


#### Jasper Tcl Files

Below is an example tcl script: 

```
# this clears previous blocks and proofs
clear -all 

# this says to initiate coverage checking, and allows you to list the modes (can also be done in gui)
check_cov -init -type all -model {branch toggle statement} -toggle_ports_only

# you must analyze all the files in your design (source and testbench) before doing anything in jasper
analyze -sv block_source.sv block_testbench.sv 

# specify the top level module, in this case the testbench 
elaborate -top fixed_point_iterative_Multiplier_sva -create_related_covers {precondition witness}

# specify clock and reset signals
clock clk
# reset reset
prove -bg -task {<embedded>}
```

Alternatively, you can find a template [here](https://github.com/cornell-c2s2/c2s2_ip/blob/main/template/jasper_template/template_run.tcl). 

Tcl scripts can be use to automate commands that would normally have to be run through the Japser GUI. This simplifies and standardizes our testing process. Note, file names need to be changed when testing other modules.


#### For Design Exploration
Incorporating formal proofs into a design file is straightforward. It allows for easy and quick testing as RTL is being written, and also helps to document your code (someone reading your code can understand passing assertions are always true for the block, which informs the reader about the design function and intention). This is as simple as using:

```
assert X
or 
assert property( X )
```
This can be added anywhere in RTL. Just make sure to include a comment to clarify the intention. 

#### For Design Verification
##### *Binding*
For organizational reasons, if you're extensively testing your block, it should be done in a separate testbench file, with the same inputs and outputs as your block. You should analyze both the files in your Tcl scripts. The top level module (in the elaborate command) will still be the top-level source file. If you want to cover several sub-modules, you may want to create a test bench for each one.  
```
module tb_example (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic [7:0] data_out
);
{Assertions and verification logic can go here}
endmodule

bind example tb_example;
```
##### *Coverage*
Coverage analysis is automatically run in the Tcl script. It can be accessed by clicking on the "+" icon next to the Formal Property Verification tab and clicking "Coverage." This will show a coverage breakdown by block. You can double click on a block to show coverage line-by-line, and switch between the different coverage models. 


#### Additional Readings
* [SVA constructs supported by Cadence](https://uobdv.github.io/Design-Verification/Quick-References/SVA_QuickReference.CDNS.pdf)
* [Tips and Best Practices for Writing a Formal Testbench](https://dvcon-proceedings.org/wp-content/uploads/1097-Demystifying-Formal-Testbenches-Tips-Tricks-and-Recommendations.pdf)
* [Jasper Template](https://github.com/cornell-c2s2/c2s2_ip/tree/main/template/jasper_template)
