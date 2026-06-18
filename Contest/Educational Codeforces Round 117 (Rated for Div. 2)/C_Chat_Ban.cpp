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

ll ut,lt,tot;

ll ut_search(ll l, ll h, ll &x){
    if(l>h) return l;
    ll mid = (l+h)/2;
    ll stars = (mid*(mid+1))/2;
    if(stars<x) return ut_search(mid+1,h,x);
    else if(stars>x)    return ut_search(l,mid-1,x);
    else return mid;
}

ll lt_search(ll l, ll h, ll &remX){
    if(l>h) return h;
    ll mid = (l+h)/2;
    ll remStars = lt - (mid*(mid+1))/2;
    if(remStars<remX)   return lt_search(l,mid-1,remX);
    else if(remStars>remX) return lt_search(mid+1,h,remX);
    else return mid;
}

void solve()
{
    ll k,x;
    cin>>k>>x;
    ut = (k*(k+1))/2, lt = (k*(k-1))/2;
    if(ut+lt<=x){
        cout<<2*k-1<<endl;
        return;
    }
    if(ut>=x){
        cout<<ut_search(1,k,x)<<endl;
        return;
    }
    x-=ut;
    cout<<2*k-1-lt_search(1,k-1,x)<<endl;
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