module CLaSH.Default

class Default a where
  def : a

instance Default Int where
  def = 0

instance Default Integer where
  def = 0
