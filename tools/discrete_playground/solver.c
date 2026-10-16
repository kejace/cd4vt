/* Numerical companion to the regular four-active-edge construction.
 * Original Lean equations and validation scope are documented in README.md.
 * All arithmetic is IEEE double; successful output is numerically checked,
 * not a proof certificate. No external solver, heap allocation or threads. */
#include <math.h>
#include <complex.h>
#include <stdint.h>
#include <string.h>
#define N 25          /* buffer stride; polygons have 4..MAXN vertices */
#define MAXN 24
#define METRICS (3*N)    /* offset of the metrics in the output buffer */
#define TAU 6.283185307179586476925286766559
#define LOWER 1e-10
#define UPPER (1.0-1e-10)
static double input[3*N], output[3*N+10];
static int evaluations, attempts, frame_mask, method;
static uint32_t random_state;
static int balanced_start;
double *input_buffer(void) { return input; }
double *output_buffer(void) { return output; }
static double uniform(void){random_state^=random_state<<13;random_state^=random_state>>17;random_state^=random_state<<5;return (random_state+0.5)/4294967296.0;}
static double norm2(const double f[3]){return f[0]*f[0]+f[1]*f[1]+f[2]*f[2];}

/* q_i = half-length / endpoint cap, κ normalized to max κ = 1.
 * Subtract the exact circular closure term before dividing by profile contrast.
 * At T=2π this is an invertible scaling of the original closure equation. */
static int residual(int n,const double *k,const double *q,double f[3],double J[3][N]){
    double cap[N],h[N],A[N],B[N],ad[N],bd[N],theta=0,P=0,T=0,contrast=1;
    double complex z[N],E=0;
    evaluations++;
    for(int i=0;i<n;i++){
        cap[i]=1/fmax(k[i],k[(i+1)%n]);h[i]=cap[i]*q[i];
        double a=k[i]*h[i],b=k[(i+1)%n]*h[i];
        if(fabs(a)>=1 || fabs(b)>=1 || q[i]<0)return 0;
        A[i]=asin(a);B[i]=asin(b);
        ad[i]=k[i]*cap[i]/sqrt(1-a*a);bd[i]=k[(i+1)%n]*cap[i]/sqrt(1-b*b);
        T+=A[i]+B[i];P+=h[i];contrast=fmin(contrast,k[i]);
    }
    contrast=1-contrast;
    if(P<=0 || contrast<=0)return 0;
    for(int i=0;i<n;i++){
        if(i)theta+=B[i-1]+A[i];
        z[i]=cos(theta)+I*sin(theta);E+=h[i]*z[i];
    }
    double complex C=sin(T/2)*(cos(T/2-A[0])+I*sin(T/2-A[0]));
    double complex R=(E-C)/contrast;
    f[0]=creal(R)/P;f[1]=cimag(R)/P;f[2]=(T-TAU)/TAU;
    for(int j=0;j<n;j++){
        double complex dE=cap[j]*z[j];
        for(int i=1;i<n;i++){
            double slope=(j<i?bd[j]:0)+(j>0 && j<=i?ad[j]:0);
            dE+=I*h[i]*z[i]*slope;
        }
        double complex dC=.5*(cos(T-A[0])+I*sin(T-A[0]))*(ad[j]+bd[j]);
        if(j==0)dC-=I*C*ad[0];
        double complex dR=(dE-dC)/contrast;
        double complex d=(dR*P-R*cap[j])/(P*P);
        J[0][j]=creal(d);J[1][j]=cimag(d);J[2][j]=(ad[j]+bd[j])/TAU;
    }
    return isfinite(norm2(f));
}
static int linear3(double A[3][3],const double *b,double *x){
    double M[3][4];for(int i=0;i<3;i++){for(int j=0;j<3;j++)M[i][j]=A[i][j];M[i][3]=b[i];}
    for(int i=0;i<3;i++){
        int p=i;for(int j=i+1;j<3;j++)if(fabs(M[j][i])>fabs(M[p][i]))p=j;
        if(fabs(M[p][i])<1e-25)return 0;
        for(int j=i;j<4;j++){double t=M[p][j];M[p][j]=M[i][j];M[i][j]=t;}
        for(int r=i+1;r<3;r++){double a=M[r][i]/M[i][i];for(int j=i;j<4;j++)M[r][j]-=a*M[i][j];}
    }
    for(int i=2;i>=0;i--){x[i]=M[i][3];for(int j=i+1;j<3;j++)x[i]-=M[i][j]*x[j];x[i]/=M[i][i];}
    return 1;
}
static int converged(int n,const double *k,const double f[3]){
    double low=1;for(int i=0;i<n;i++)low=fmin(low,k[i]);
    double tol=fmax(8e-12,8e-16/(1-low));
    return fabs(f[0])<tol && fabs(f[1])<tol && fabs(f[2])<3e-12;
}
/* Bounded damped minimum-norm Newton. The active mask freezes dormant
 * coordinates during anchor construction/opening; continuation frees all. */
static int correct(int n,const double *k,double *q,int mask,int maxiter){
    double f[3],J[3][N],lambda=1e-7;
    if(!residual(n,k,q,f,J))return 0;
    for(int iter=0;iter<maxiter;iter++){
        if(converged(n,k,f))return 1;
        double weight[N],G[3][3]={{0}},gradient[N]={0};
        for(int j=0;j<n;j++){
            for(int r=0;r<3;r++)gradient[j]+=J[r][j]*f[r];
            weight[j]=(mask&(1<<j))?1:0;
            if((q[j]<LOWER*10 && gradient[j]>0)||(q[j]>1-LOWER*10 && gradient[j]<0))weight[j]=0;
            for(int r=0;r<3;r++)for(int s=0;s<3;s++)G[r][s]+=weight[j]*J[r][j]*J[s][j];
        }
        double trace=G[0][0]+G[1][1]+G[2][2],previous=norm2(f);int accepted=0;
        for(int trial=0;trial<10;trial++){
            double H[3][3],x[3],step[N],alpha=1;
            memcpy(H,G,sizeof H);for(int r=0;r<3;r++)H[r][r]+=lambda*fmax(trace/3,1e-8);
            if(!linear3(H,f,x)){lambda*=10;continue;}
            for(int j=0;j<n;j++){
                step[j]=0;for(int r=0;r<3;r++)step[j]-=weight[j]*J[r][j]*x[r];
                if(fabs(step[j])>.25)alpha=fmin(alpha,.25/fabs(step[j]));
                if(step[j]>0)alpha=fmin(alpha,.995*(UPPER-q[j])/step[j]);
                if(step[j]<0)alpha=fmin(alpha,.995*(LOWER-q[j])/step[j]);
            }
            for(int back=0;back<12;back++){
                double candidate[N],nf[3],nj[3][N];
                for(int j=0;j<n;j++)candidate[j]=q[j]+alpha*step[j];
                if(alpha>1e-14 && residual(n,k,candidate,nf,nj) && norm2(nf)<previous){
                    memcpy(q,candidate,n*sizeof(double));memcpy(f,nf,sizeof f);memcpy(J,nj,sizeof J);
                    lambda=fmax(1e-14,lambda*.18);accepted=1;break;
                }
                alpha*=.5;
            }
            if(accepted)break;
            lambda=fmin(1e10,lambda*20);
        }
        if(!accepted)return 0;
    }
    return converged(n,k,f);
}
/* Independent geometric check: vertices, cyclic triple curvatures, all
 * supporting half-planes, both endpoint caps, position and lifted turning. */
static int inspect(int n,const double *k,const double *ell,int publish){
    double x[N],y[N],turn=0,heading=0,px=0,py=0,P=0,maxlen=0,minlen=INFINITY,margin=1;
    for(int i=0;i<n;i++){
        if(!(ell[i]>0) || !isfinite(ell[i]))return 0;
        margin=fmin(margin,1-ell[i]*fmax(k[i],k[(i+1)%n])/2);
        if(margin<=0)return 0;
        double angle=asin(k[i]*ell[(i+n-1)%n]/2)+asin(k[i]*ell[i]/2);
        turn+=angle;if(i)heading+=angle;
        x[i]=px;y[i]=py;px+=ell[i]*cos(heading);py+=ell[i]*sin(heading);
        P+=ell[i];maxlen=fmax(maxlen,ell[i]);minlen=fmin(minlen,ell[i]);
    }
    double closure=hypot(px,py)/P,turnerr=fabs(turn-TAU),curverr=0,support=INFINITY;
    for(int i=0;i<n;i++){
        int prev=(i+n-1)%n,next=(i+1)%n;
        double ux=x[i]-x[prev],uy=y[i]-y[prev],vx=x[next]-x[i],vy=y[next]-y[i];
        double denom=hypot(ux,uy)*hypot(vx,vy)*hypot(ux+vx,uy+vy);
        if(denom<=0)return 0;
        double measured=2*(ux*vy-uy*vx)/denom;
        curverr=fmax(curverr,fabs(measured/k[i]-1));
        for(int j=0;j<n;j++)if(j!=i && j!=next){
            double cross=vx*(y[j]-y[i])-vy*(x[j]-x[i]);
            support=fmin(support,cross/(P*P));
        }
    }
    int valid=closure<2e-10 && turnerr<3e-10 && curverr<2e-6 && margin>2e-10 && minlen/maxlen>2e-8 && support>0;
    if(publish){
        for(int i=0;i<n;i++){output[i]=ell[i];output[N+2*i]=x[i];output[N+2*i+1]=y[i];}
        output[METRICS]=closure;output[METRICS+1]=turnerr;output[METRICS+2]=curverr;output[METRICS+3]=margin;output[METRICS+4]=minlen/maxlen;output[METRICS+5]=evaluations;output[METRICS+6]=attempts;output[METRICS+7]=method;output[METRICS+8]=frame_mask;output[METRICS+9]=support;
    }
    return valid;
}
static int admissible(int n,const double *k){
    for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)if(k[i]!=k[j]){
        double c=(k[i]+k[j])/2;int changes=0;
        for(int r=0;r<n;r++)if((k[r]>c)!=(k[(r+1)%n]>c))changes++;
        if(changes>=4)return 1;
    }
    int constant=1;for(int i=1;i<n;i++)if(k[i]!=k[0])constant=0;return constant;
}
static int constant_solution(int n,const double *k,const double *previous,double *ell){
    if(!previous){for(int i=0;i<n;i++)ell[i]=2*sin(TAU/(2*n))/k[0];return 1;}
    double hi=INFINITY,lo=0;
    for(int i=0;i<n;i++){if(!(previous[i]>0))return 0;hi=fmin(hi,2/(k[0]*previous[i]));}
    hi*=UPPER;double total=0;for(int i=0;i<n;i++)total+=2*asin(k[0]*previous[i]*hi/2);
    if(total<TAU)return 0;
    for(int t=0;t<60;t++){double mid=(lo+hi)/2;total=0;for(int i=0;i<n;i++)total+=2*asin(k[0]*previous[i]*mid/2);if(total>TAU)hi=mid;else lo=mid;}
    for(int i=0;i<n;i++)ell[i]=previous[i]*(lo+hi)/2;
    return 1;
}
static void normalized(int n,const double *k,double *kn,double *caps,double *scale){
    *scale=0;for(int i=0;i<n;i++)*scale=fmax(*scale,k[i]);
    for(int i=0;i<n;i++)kn[i]=k[i]/(*scale);
    for(int i=0;i<n;i++)caps[i]=1/fmax(kn[i],kn[(i+1)%n]);
}
static int initialize(int n,const double *k,double *ell){
    double kn[N],caps[N],scale;normalized(n,k,kn,caps,&scale);
    int boundary[N],m=0;for(int i=0;i<n;i++)if(k[i]!=k[(i+1)%n])boundary[m++]=i;
    if(!m){method=1;return constant_solution(n,k,0,ell);}
    struct frame{int mask;double score;} frames[N*N];int nf=0;
    for(int a=0;a<m;a++)for(int b=a+1;b<m;b++){
        if(b==a+1 || (a==0 && b==m-1))continue;
        int mask=(1<<boundary[a])|(1<<boundary[(a+m-1)%m])|(1<<boundary[b])|(1<<boundary[(b+m-1)%m]);
        double q[N]={0},f[3],J[3][N];for(int i=0;i<n;i++)if(mask&(1<<i))q[i]=UPPER;
        if(!residual(n,kn,q,f,J)||f[2]<=0)continue;
        frames[nf++]=(struct frame){mask,fmin(kn[boundary[a]],kn[boundary[b]])+.1*fmax(kn[boundary[a]],kn[boundary[b]])};
    }
    for(int a=0;a<nf;a++)for(int b=a+1;b<nf;b++)if(frames[b].score>frames[a].score){struct frame tmp=frames[a];frames[a]=frames[b];frames[b]=tmp;}
    for(int pass=0;pass<2;pass++)for(int fi=0;fi<nf;fi++)for(int attempt=0;attempt<(pass?14:4);attempt++){
        int mask=frames[fi].mask;double q[N]={0},f[3],J[3][N];attempts++;
        for(int i=0;i<n;i++)if(mask&(1<<i))q[i]=attempt==0 && balanced_start?UPPER:(pass?.12+.87*uniform():.7+.29*uniform());
        if(!residual(n,kn,q,f,J))continue;
        if(f[2]>0){double lo=0,hi=1;for(int t=0;t<35;t++){double mid=(lo+hi)/2,z[N];for(int i=0;i<n;i++)z[i]=mid*q[i];residual(n,kn,z,f,J);if(f[2]>0)hi=mid;else lo=mid;}for(int i=0;i<n;i++)q[i]*=(lo+hi)/2;}
        if(!correct(n,kn,q,mask,180))continue;
        double epsilons[]={.04,.01,.002,.0002,.00002};
        for(int e=0;e<5;e++){
            double z[N];memcpy(z,q,n*sizeof(double));for(int i=0;i<n;i++)if(!(mask&(1<<i)))z[i]=epsilons[e];
            if(!correct(n,kn,z,mask,120))continue;
            for(int i=0;i<n;i++)ell[i]=2*caps[i]*z[i]/scale;
            if(inspect(n,k,ell,0)){frame_mask=mask;method=2;return 1;}
        }
    }
    return 0;
}
static int continuation(int n,const double *oldk,const double *oldell,const double *target,double *ell){
    double t=0,dt=1,previous[N];memcpy(previous,oldell,n*sizeof(double));
    if(!inspect(n,oldk,oldell,0))return 0;
    for(int iter=0;t<1-1e-14 && iter<160;iter++){
        double next=fmin(1,t+dt),k[N],kn[N],caps[N],scale,q[N],candidate[N];int constant=1,inside=1;
        for(int i=0;i<n;i++)k[i]=oldk[i]+next*(target[i]-oldk[i]);
        for(int i=1;i<n;i++)if(k[i]!=k[0])constant=0;
        normalized(n,k,kn,caps,&scale);
        int ok=0;
        if(constant)ok=constant_solution(n,k,previous,candidate);
        else{
            for(int i=0;i<n;i++){q[i]=previous[i]*scale/(2*caps[i]);if(q[i]>=UPPER || q[i]<=LOWER)inside=0;}
            if(inside && correct(n,kn,q,(1<<n)-1,55)){
                for(int i=0;i<n;i++)candidate[i]=2*caps[i]*q[i]/scale;
                ok=1;
            }
        }
        if(ok){
            double movement=0;for(int i=0;i<n;i++)movement=fmax(movement,fabs(log(candidate[i]/previous[i])));
            ok=movement<.35 && inspect(n,k,candidate,0);
        }
        if(ok){memcpy(previous,candidate,n*sizeof(double));t=next;dt=fmin(1-t,dt*1.7);}
        else dt*=.5;
        if(dt<1e-7 && t<1-1e-14)return 0;
    }
    if(t<1-1e-14)return 0;
    memcpy(ell,previous,n*sizeof(double));method=3;return 1;
}
/* Input: new κ[0:N], previous κ[N:2N], previous full lengths[2N:3N].
 * Output: lengths[0:N], vertices[N:3N], metrics[3N:3N+10].
 * Return 1 success, -1 size, -2 numeric range, -3 DFV, -4 branch ended,
 * 0 bounded initializer exhausted. No failure means nonexistence. */
int solve(int n,int mode,int seed){
    evaluations=attempts=frame_mask=method=0;memset(output,0,sizeof output);
    balanced_start=seed==17;
    random_state=(uint32_t)seed+0x9e3779b9u;if(!random_state)random_state=1;
    if(n<4 || n>MAXN)return -1;
    double lo=INFINITY,hi=0,ell[N];
    for(int i=0;i<n;i++){if(!isfinite(input[i]) || input[i]<=0)return -2;lo=fmin(lo,input[i]);hi=fmax(hi,input[i]);}
    if(lo<1e-6 || hi>1e6 || hi/lo>10000)return -2;
    if(!admissible(n,input))return -3;
    int ok=mode?continuation(n,input+N,input+2*N,input,ell):initialize(n,input,ell);
    output[METRICS+5]=evaluations;output[METRICS+6]=attempts;
    if(!ok)return mode?-4:0;
    return inspect(n,input,ell,1)?1:(mode?-4:0);
}
/* Exposed for independent Jacobian tests, never used by the product UI. */
int evaluate(int n){double f[3],J[3][N];if(n<4||n>MAXN)return 0;if(!residual(n,input,input+N,f,J))return 0;for(int r=0;r<3;r++){output[r]=f[r];for(int i=0;i<n;i++)output[3+r*N+i]=J[r][i];}return 1;}
