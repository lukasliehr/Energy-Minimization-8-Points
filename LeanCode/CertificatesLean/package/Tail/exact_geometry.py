"""Boundary geometry in a diagonal rescaling of the Fourier slice.

Every coefficient belongs exactly to Q(sqrt(2)); no root enclosure is used.
The displacement column is (X/r,Y/r,Z/h), with r^2=1-a,h^2=a.
"""
from dihedral_basis import K, T


def geometry():
    a = (2*T-1)/7
    cs = [K(1),T/2,K(),-T/2,K(-1),-T/2,K(),T/2]
    sn = [K(),T/2,K(1),T/2,K(),-T/2,K(-1),-T/2]
    sg = [(-1)**i for i in range(8)]
    invroot8 = T/4
    columns = []

    def mode(coordinate, wave, frequency=1):
        out=[]
        for i in range(8):
            w = wave[(frequency*i)%8]
            if coordinate == 0:
                out.append((-sn[i]*w,cs[i]*w,K()))
            else:
                out.append((-cs[i]*w,-sn[i]*w,sg[i]*w))
        return out

    columns.append(mode(1,[invroot8]*8))
    for frequency in (1,2):
        for coordinate in (0,1):
            for wave in (cs,sn):
                columns.append(mode(coordinate,[v/2 for v in wave],frequency))
    columns.append([((-sn[i]*sn[3*i%8]-a*cs[i]*cs[3*i%8])/2,
                     (cs[i]*sn[3*i%8]-a*sn[i]*cs[3*i%8])/2,
                     sg[i]*a*cs[3*i%8]/2) for i in range(8)])
    columns.append([((-sn[i]*cs[3*i%8]+a*cs[i]*sn[3*i%8])/2,
                     (cs[i]*cs[3*i%8]+a*sn[i]*sn[3*i%8])/2,
                     -sg[i]*a*sn[3*i%8]/2) for i in range(8)])
    for coordinate in (0,1):
        columns.append(mode(coordinate,[v*invroot8 for v in sg]))
    U = [list(x) for x in zip(*columns)]
    # These identities follow by multiplying out with T^2=2.
    az,mer,third = 1+T/4,2+9*T/4,1+T/2
    weights=[mer,az,az,mer,mer,az,az,mer,mer,third,third,az,mer]

    def dot(x,y):
        return az*(x[0]*y[0]+x[1]*y[1])+(1+2*T)*x[2]*y[2]

    def pdot(i,v):
        return cs[i]*v[0]+sn[i]*v[1]+sg[i]*v[2]

    edges=[(0,1),(0,2)]
    R=[]; M=[]; incidence=[]
    for i,j in edges:
        R.append([-2*(pdot(j,U[i][k])+pdot(i,U[j][k])) for k in range(13)])
        Q=[[dot(U[i][k],U[i][l])+dot(U[j][k],U[j][l]) for l in range(13)] for k in range(13)]
        incidence.append(Q)
        M.append([[a*Q[k][l]-dot(U[i][k],U[j][l])-dot(U[j][k],U[i][l])
                   for l in range(13)] for k in range(13)])
    return dict(a=a,weights=weights,columns=U,edges=edges,R=R,M=M,T=incidence,dot=dot,pdot=pdot)
