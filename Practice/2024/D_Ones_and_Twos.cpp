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
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl

/****************************************************************/

typedef long double ld;
typedef unsigned int ui;
typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;
typedef vector<int> vi;
typedef vector<long long> vll;

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
const int N = 1e5+5;
vi v(N), tree(3*N);
bool flag;

void checkifSumExists(int node, int l, int h, int &sum){
    if(tree[node]<sum)  return;
    if(l==h&&tree[node]!=sum)   return;
    if(tree[node]==sum) {flag = true; return;}
    int mid = (l+h)/2;
    int left = 2*node, right = 2*node+1;
    checkifSumExists(left, l, mid, sum);
    checkifSumExists(right, mid+1, h, sum);
}

void makeSegTree(int node, int l , int h){
    if(l==h){
        tree[node] = v[l];
        return;
    }
    int mid = (l+h)/2;
    int left = 2*node, right = 2*node+1;
    makeSegTree(left, l, mid);
    makeSegTree(right, mid+1, h);
    tree[node] = tree[left]+tree[right];
}

void update(int node, int l, int h, int &i, int &val){
    if(l>i||h<i)    return;
    if(l==i && h == i){
        tree[node] = val;
        return;
    }
    int mid = (l+h)/2;
    int left = 2*node, right = 2*node+1;
    update(left, l, mid, i, val);
    update(right, mid+1, h, i, val);
    tree[node] = tree[left]+tree[right];
}

void solve()
{
    int n,q,type, a,b;
    cin>>n>>q;
    rep(i,1,n+1) cin>>v[i];
    makeSegTree(1,1,n);
    for(int i = 1; i<3*n; i++)  cout<<tree[i]<<" ";
    cout<<endl;
    while(q--){
        cin>>type>>a;
        if(type==2) cin>>b;
        if(type==2) update(1,1,n,a,b);
        else{
            flag = false;
            checkifSumExists(1,1,n,a);
            if(flag)    yes;
            else no;
        }
    }
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