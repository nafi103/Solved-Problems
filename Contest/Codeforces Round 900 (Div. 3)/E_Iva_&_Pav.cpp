#include <bits/stdc++.h>
using namespace std;

/********************************Macros********************************/

#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define ff first
#define ss second
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
#define int long long
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl

/****************************************************************/

typedef long double ld;
typedef unsigned int ui;
typedef unsigned long long ull;
typedef long double lld;
typedef vector<int> vi;
typedef vector<long long> vll;
typedef vector<pair<int,int>> vpi;

/********************************Debugger********************************/

#ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
#else
#define debug(x)
#endif

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
int n,L,k;

void makeBitVector(vector<vector<int>>&v,int &n){
    rep(i,0,31){
        v[0].pb(0);
    }
    rep(i,1,n+1){
        int x;
        cin>>x;
        while(x>0){
            v[i].pb(x%2);
            x>>=1;
        }
        rep(j,v[i].size(),31){
            v[i].pb(0);
        }
    }
    rep(i,2,n+1){
        rep(j,0,31){
            v[i][j]+=v[i-1][j];
        }
    }
}

int value(vector<int>&vr, vector<int>&vl,int y){
    int ans = 0;
    rep(i,0,31){
        if(vr[i]-vl[i]==y)    ans+=(1<<i);
    }
    return ans;
}

bool check(vector<vector<int>> &v,int pos)
{
    return value(v[pos],v[L-1],pos-L+1)>=k;
}

int bs(vector<vector<int>> &v,int l,int r){
    if(l>r) return r;
    int mid = (l+r)/2;
    debug(mid)
    if(check(v,mid))  return bs(v,mid+1,r);
    else return bs(v,l, mid-1);
}

void solve()
{
    cin>>n;
    vector<vector<int>> v(n+1,vector<int>());
    makeBitVector(v,n);
    int q;
    cin>>q;
    while(q--){
        cin>>L>>k;
        if (value(v[L], v[L - 1], 1)<k){
            cout<<-1<<" ";
        }else{
            cout<<bs(v,L,n)<<" ";
            debug(endl)
        }
    }
    cout<<endl;
}

int32_t main()
{
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    while (t--)
        solve();
}