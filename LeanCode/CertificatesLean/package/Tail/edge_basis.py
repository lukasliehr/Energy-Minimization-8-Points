"""Explicit unnormalized +/- bases for the two edge stabilizer reflections."""
from dihedral_basis import K,linear_action


def edge_features(distance):
    if distance not in (1,2):raise ValueError('contact distance1 or2 required')
    action=linear_action(distance,True)
    plus=[{():K(1)},{(0,):K(1)}];minus=[]
    for i,j in [(1,2),(3,4),(5,6),(7,8),(9,10)]:
        c,s=action[i+1][i+1],action[i+1][j+1]
        # This one explicitly identified block is diag(-1,1).
        if distance==2 and i==7:
            p={(j,):K(1)};m={(i,):K(1)}
        else:
            p={(i,):1+c,(j,):s};m={(i,):-s,(j,):1+c}
            p={k:v for k,v in p.items()if v};m={k:v for k,v in m.items()if v}
        plus.append(p);minus.append(m)
    plus.append({((11 if distance==1 else 12),):K(1)})
    minus.append({((12 if distance==1 else 11),):K(1)})
    return [('+',plus),('-',minus)]
