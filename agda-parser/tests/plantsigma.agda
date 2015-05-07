module plantsigma where


data Tree : Set where
  oak    : Tree
  pine   : Tree
  spruce : Tree

data Flower : Set where
  rose : Flower
  lily : Flower


data PlantGroup : Set where
  tree   : PlantGroup
  flower : PlantGroup


PlantsInGroup : PlantGroup -> Set
PlantsInGroup tree   = Tree
PlantsInGroup flower = Flower


data Plant : Set where
  plant : (g : PlantGroup) -> PlantsInGroup g -> Plant

f : Plant -> PlantGroup
f (plant g pg) = g
   