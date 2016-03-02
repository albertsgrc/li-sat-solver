fs = require 'fs'
child = require 'child_process'

THRESHOLD = 250

e = child.execSync

instances = fs.readdirSync './instances'

###

e("make")

for instance in instances when Number(instance.match(/^vars-(\d{3})-.*\.cnf$/)[1]) <= THRESHOLD
    try
        e("./solver < instances/#{instance} > stats.txt")
    catch err


    stats = fs.readFileSync "./stats.txt", "utf-8"

    console.log instance
    console.log "------------------"
    console.log stats

e("rm -f ./stats.txt")

###
