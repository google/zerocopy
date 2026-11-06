Carbon
===

Carbon is a verification-condition-generation-based verifier for [the Viper intermediate verification language](https://github.com/viperproject/silver).

[The Viper project](http://www.pm.inf.ethz.ch/research/viper.html) is developed by the [Programming Methodology](http://www.pm.inf.ethz.ch/) group at ETH Zurich.

See [the documentation wiki](https://github.com/viperproject/documentation/wiki) for instructions on how to try out or install the Viper tools.

Installation Instructions:
---

We recommend using carbon through the [VS Code plugin](https://marketplace.visualstudio.com/items?itemName=viper-admin.viper). Alternatively, one can compile carbon from source with the following steps:

* Install Z3 and Boogie and set the environment variables `Z3_EXE` and `BOOGIE_EXE` correspondingly (see wiki above)
* Clone this repository *recursively* by running:  
`git clone --recursive https://github.com/viperproject/carbon`

And then  
* Compile and run with:  
  `sbt "run [options] <path to Viper file>"`
* Alternatively, for a faster startup without compilation each time, build a `.jar` file:  
  `sbt assembly`  
  And then run with:  
  `java -jar ./target/scala-*/carbon.jar [options] <path to Viper file>`
