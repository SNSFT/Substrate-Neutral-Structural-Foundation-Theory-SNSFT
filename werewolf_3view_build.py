import numpy as np;from PIL import Image;from scipy import ndimage as ndi
im=np.array(Image.open('sheet.webp').convert('RGB')).astype(float)
bg=np.array([107,108,109.])
def mask(x0,x1,y0=10,y1=690,thr=22):
    c=im[y0:y1,x0:x1];d=np.sqrt(((c-bg)**2).sum(2))
    # local background: smooth gray, low saturation, near bg
    fg=d>thr
    yy=np.arange(c.shape[0])[:,None];fg&=~((yy>c.shape[0]-40)&(d<45))   # floor shadow under the feet
    fg=ndi.binary_closing(fg,iterations=2)
    holes=ndi.binary_fill_holes(fg)&~fg;hl,hn=ndi.label(holes);hs=ndi.sum(holes,hl,range(1,hn+1))
    fg|=np.isin(hl,1+np.where(hs<600)[0]);fg=ndi.binary_opening(fg,iterations=1)
    lab,n=ndi.label(fg);sz=ndi.sum(fg,lab,range(1,n+1));keep=np.isin(lab,1+np.where(sz>300)[0])
    return keep,c
F,cf=mask(5,400);B,cb=mask(400,740);S,cs=mask(745,1020)
for n,m in [('front',F),('back',B),('side',S)]:
    ys,xs=np.where(m);print(n,m.shape,'bbox y',ys.min(),ys.max(),'x',xs.min(),xs.max(),'area',m.sum())
    Image.fromarray((m*255).astype(np.uint8)).save(n+'_mask.png')
np.savez('masks.npz',F=F,B=B,S=S,cf=cf,cb=cb,cs=cs)
import numpy as np,trimesh;from PIL import Image;from scipy import ndimage as ndi
d=np.load('masks.npz');F,B,S,cf,cb=d['F'],d['B'],d['S'],d['cf'],d['cb']
H,W=F.shape
def bbox(m):ys,xs=np.where(m);return ys.min(),ys.max(),xs.min(),xs.max()
fy0,fy1,fx0,fx1=bbox(F);by0,by1,bx0,bx1=bbox(B);sy0,sy1,sx0,sx1=bbox(S)
# ---- back view: mirror and map onto the front frame (colors only; the front silhouette is the master outline)
cbm=cb[:,::-1];Bm=B[:,::-1];bx0m,bx1m=B.shape[1]-1-bx1,B.shape[1]-1-bx0
def back_color(r,x):
    rr=by0+(r-fy0)*(by1-by0)/(fy1-fy0);xx=bx0m+(x-fx0)*(bx1m-bx0m)/(fx1-fx0)
    rr=np.clip(rr,0,cbm.shape[0]-1).astype(int);xx=np.clip(xx,0,cbm.shape[1]-1).astype(int)
    return cbm[rr,xx],Bm[rr,xx]
# ---- side view: per-row front/back depth, body axis tracked from the chest
sc=(sy1-sy0)/(fy1-fy0)
def runs(a):return [] if len(a)==0 else [(s[0],s[-1]) for s in np.split(a,np.where(np.diff(a)>1)[0]+1)]
axis=np.median([ (lambda R:(max(R,key=lambda q:q[1]-q[0])[0]+max(R,key=lambda q:q[1]-q[0])[1])/2)(runs(np.where(S[r])[0])) for r in range(150,350)])
hi=np.full(H,np.nan);lo=np.full(H,np.nan);ph=None;sep_rows=[]
for r in range(H):
    sr=int(round(sy0+(r-fy0)*sc))
    if r<fy0 or r>fy1 or sr<0 or sr>=S.shape[0]:continue
    R=[q for q in runs(np.where(S[sr])[0]) if q[1]-q[0]>=4]
    if not R:continue
    longR=[q for q in R if q[1]-q[0]>15]
    if r>450 and len(longR)>=2:q=max(longR,key=lambda q:q[1]);sep_rows.append(r)   # legs are the front-most run; the tail hangs behind
    else:q=max(R,key=lambda q:q[1]-q[0])
    h_,l_=float(q[1]),float(q[0])
    if r>300 and ph is not None:h_=min(h_,ph+0.15)   # hands and claws do not widen the body
    hi[r]=h_;lo[r]=l_;ph=h_
# tail-aware back edge: from the waist down to where the legs separate from the tail, interpolate
rs=min(sep_rows) if sep_rows else None
if rs:
    rh=300+int(np.nanargmax(lo[300:rs]))
    lo[rh:rs]=np.linspace(lo[rh],np.nanmedian(lo[rs:rs+20]),rs-rh)
ok=~np.isnan(hi);rr=np.arange(H)
hi=np.interp(rr,rr[ok],hi[ok]);lo=np.interp(rr,rr[ok],lo[ok])
hi=ndi.gaussian_filter1d(ndi.median_filter(hi,21),6);lo=ndi.gaussian_filter1d(ndi.median_filter(lo,21),6)
mid=(hi+lo)/2-axis;half=(hi-lo)/2
# ---- front silhouette inflation with a local radius, so arms come out thinner than the torso
dist=ndi.distance_transform_edt(F)
Rl=np.maximum(ndi.maximum_filter(dist,size=41),dist)
hh=np.sqrt(np.maximum(0,2*Rl*dist-dist**2))
Rrow=np.maximum(ndi.maximum_filter1d(hh.max(1),31),1)[:,None]
t=np.clip(hh/Rrow,0,1)
# smooth the form vertically inside the outline so the crotch and armpits do not step
Fm=F.astype(float);t=ndi.gaussian_filter(t*Fm,(7,2))/np.maximum(ndi.gaussian_filter(Fm,(7,2)),1e-6)*Fm
t=np.minimum(t,np.sqrt(np.clip(dist/6,0,1)))   # still meets the outline at zero
# colors: sample from inside the outline so the background fringe never tints the edge
inner=ndi.binary_erosion(F,iterations=3)
_,(iy,ix)=ndi.distance_transform_edt(~inner,return_indices=True)
cf=cf[iy,ix]
# skin detail: fine luminance detail (fur), small amplitude
def lum(c):return (0.2126*c[...,0]+0.7152*c[...,1]+0.0722*c[...,2])/255
Lf=lum(cf);detf=Lf-ndi.gaussian_filter(Lf,4)
rows=np.arange(H)[:,None];cols=np.arange(W)[None,:]
bcol,bm=back_color(rows+0*cols,cols+0*rows);bin_=ndi.binary_erosion(bm,iterations=3);_,(jy,jx)=ndi.distance_transform_edt(~bin_,return_indices=True);bcol=bcol[jy,jx];Lb=lum(bcol);detb=Lb-ndi.gaussian_filter(Lb,4)
zF=mid[:,None]+half[:,None]*t+6*detf*t; zB=mid[:,None]-(half[:,None]*t+6*detb*t)
# ---- mesh on a downsampled grid, front and back stitched along the outline
k=3;G0=F[::k,::k].copy()
Q=G0[:-1,:-1]&G0[1:,:-1]&G0[:-1,1:]&G0[1:,1:]
Q=ndi.binary_opening(Q,iterations=1)
for it in range(50):  # remove pinch points: diagonal-only quad contacts
    a1=Q[:-1,:-1]&Q[1:,1:]&~Q[1:,:-1]&~Q[:-1,1:];a2=Q[1:,:-1]&Q[:-1,1:]&~Q[:-1,:-1]&~Q[1:,1:]
    if not a1.any() and not a2.any():break
    jj,ii=np.where(a1);Q[jj+1,ii]=True;jj,ii=np.where(a2);Q[jj,ii]=True
lab,nl=ndi.label(Q);sz=ndi.sum(Q,lab,range(1,nl+1));Q=lab==(1+np.argmax(sz))
G=np.zeros_like(G0);G[:-1,:-1]|=Q;G[1:,:-1]|=Q;G[:-1,1:]|=Q;G[1:,1:]|=Q;g=G.shape
idx=-np.ones(g,int);ys,xs=np.where(G);n=len(ys);idx[ys,xs]=np.arange(n)
R0,C0=ys*k,xs*k
pos_f=np.c_[C0-(fx0+fx1)/2,-(R0-fy1),zF[R0,C0]];pos_b=np.c_[C0-(fx0+fx1)/2,-(R0-fy1),zB[R0,C0]]
col_f=cf[R0,C0];col_b=bcol[R0,C0]
V=np.vstack([pos_f,pos_b]);Cc=np.vstack([col_f,col_b])
tri=[];edges={}
for j in range(g[0]-1):
    for i in range(g[1]-1):
        if not Q[j,i]:continue
        a_,b_,c_,d_=idx[j,i],idx[j,i+1],idx[j+1,i],idx[j+1,i+1]
        for (p,q,r) in [(a_,c_,b_),(b_,c_,d_)]:
            tri.append((p,q,r));tri.append((p+n,r+n,q+n))
            for e in [(p,q),(q,r),(r,p)]:
                key=tuple(sorted(e));edges[key]=edges.get(key,0)+1
for (p,q),cnt in edges.items():
    if cnt==1:tri.append((p,q,q+n));tri.append((p,q+n,p+n))
T=np.array(tri)
# side texture: faces turned sideways take their color from the side view (mapped onto both flanks)
cs=d['cs'].astype(float);Sin=ndi.binary_erosion(S,iterations=3);_,(ky,kx)=ndi.distance_transform_edt(~Sin,return_indices=True);cs=cs[ky,kx]
tmp=trimesh.Trimesh(vertices=V,faces=T,process=False);trimesh.repair.fix_normals(tmp);Nv=tmp.vertex_normals
rowsV=fy1-V[:,1];srow=np.clip(np.round(sy0+(rowsV-fy0)*sc),0,S.shape[0]-1).astype(int)
scol=np.clip(np.round(V[:,2]+axis),0,S.shape[1]-1).astype(int)
wside=np.clip((np.abs(Nv[:,0])-0.35)/0.5,0,1)**1.5
Cc=(1-wside[:,None])*Cc+wside[:,None]*cs[srow,scol]
s=2.4/(fy1-fy0)  # 2.4 m tall, from the sheet's scale reference
m=trimesh.Trimesh(vertices=V*s,faces=T,vertex_colors=np.c_[Cc.astype(np.uint8),np.full(len(Cc),255,np.uint8)],process=False)
trimesh.repair.fix_normals(m)
trimesh.smoothing.filter_taubin(m,lamb=0.5,nu=-0.53,iterations=12)   # removes the pixel staircase along the outline
print('verts',len(m.vertices),'faces',len(m.faces),'watertight',m.is_watertight,'extents m',np.round(m.extents,3))
# glTF is Y-up: our axes are x right, y up, z toward viewer already
m.export('werewolf_exemplar.glb',include_normals=True);m.export('werewolf_exemplar.stl')
import os;print('glb bytes',os.path.getsize('werewolf_exemplar.glb'))
np.savez('depth.npz',hi=hi,lo=lo)
