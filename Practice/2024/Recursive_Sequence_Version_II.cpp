#include <bits/stdc++.h>
using namespace std;

/********************************Macros********************************/

#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define ff first
#define ss second
#define vi vector<int>
#define vll vector<long long>
#define set_bits(x) __builtin_popcount(x)
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl

/****************************************************************/

typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;

/********************************Debugger********************************/

#ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
#else
#define debug(x)
#endif

void _print(ll t) {cerr << t;}
void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}

template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}

/****************************************************************/
vector<ll>b,c;
ll k,mod;

vector<vll>multiply(vector<vll>A,vector<vll>B){
    vector<vll>ans(k,vll(k,0));
    for(int i = 0; i<k; i++){
        for(int j = 0; j<k; j++){
            for(int x = 0; x<k;x++){
                ans[i][j] = (ans[i][j] + (1LL* A[i][x] * B[x][j]) % mod) % mod;
            }
        }
    }
    return ans;
}

vector<vll>matExp(vector<vll>T, ll n){
    if(n==0){
        rep(i,0,k){
            T[0][i] = 0;
        }
        return T;
    }
    if(n==1)    return T;
    if(n&1){
        return multiply(T,matExp(T,n-1));
    }
    T = multiply(T,T);
    return matExp(T,n>>1);
}

ll compute(ll n){
    if(n<=k){
        return b[n-1];
    }
    vector<vll>T(k,vll (k,0));
    rep(i,0,k-1){
        T[i][i+1] = 1;
    }
    rep(i,0,k){
        T[k-1][k-1-i] = c[i];
    }
    T = matExp(T,n-1);
    ll ans = 0;
    rep(i,0,k){
        ans = (ans + (T[0][i]*b[i])%mod)%mod;
    }
    return ans;
}

void solve()
{
    ll x,N,M;
    cin>>k;
    rep(i,0,k){
        cin>>x;
        b.pb(x);
    }
    rep(i,0,k){
        cin>>x;
        c.pb(x);
    }
    cin>>M>>N>>mod;
    ll L = compute(M-1);
    ll R = compute(N+2);
    debug(L)    debug(R)
    cout<<R-L<<endl;
    b.clear();
    c.clear();
}

int32_t main()
{
    fastIO;
//  cout.precision(10);
//  cout.setf(ios::fixed);
    int t;
    cin >> t;
    while (t--)
        solve();
}