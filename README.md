# Práctica 1 - Sat Solver

Se han implementado las siguientes optimizaciones:

- *Vectores de clausulas donde aparece una variable negada y afirmada*: para
  hacer más rápida la propagación mirando sólo las clausulas donde aparece
  la decisión negada.

- *Heurística de actividad*: Inicialmente, se define un score por cada variable
  igual al número de apariciones de esta. Luego, a medida que se van tomando decisiones,
  se incrementa el score de una variable cuando esta se ve involucrada en un conflicto,
  para que, al decidir la variable siguiente a propagar, se propague la que tenga 
  el score más grande de entre las no definidas. Lo que se hace normalmente es decrementar 
  periódicamente los scores para olvidar conflictos que han ocurrido hace mucho tiempo, 
  pero haciendo pruebas he llegado a la conclusión que con las instancias que tenemos 
  (supongo que será algo relacionado con el hecho de que sea *random* 3 sat), 
  el tiempo de ejecución es menor si no se olvidan los scores.

- *Bit hacks*: He optimizado los métodos current_value_in_model, set_lit_to_true,
  y el bucle más interno de propagate con bit twiddling hacks. El hecho es que
  haciendo profiling del solver me di cuenta que había mucho gasto de tiempo
  por saltos (if/else) en estas funciones, por lo que decidí optimizarlas
  con bit hacks que evitaran las condiciones con saltos. El speedup que conseguí
  fue más que suficiente como para justificar la pérdida de legibilidad,
  y es que el tiempo de ejecución se redució a casi la mitad.

Benchmarks realizados en un Intel Core i5-3317U 2.6GHz
