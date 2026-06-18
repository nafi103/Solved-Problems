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

vll v(150005), psum(150005);

void solve()
{
    int n;
    ll ans = LLONG_MIN;
    cin>>n;
    rep(i,0,n){
        cin>>v[i];
    }
    for(int i = 1; i<=n; i++){
        psum[i] = v[i-1]+psum[i-1];
    }
    int sz = (n+1)/2;
    for(int i = 1; i<=sz; i++){
        if(n%i==0){
            ll mmx = LLONG_MIN, mmn = LLONG_MAX;
            for(int j = i; j<=n; j+=i){
                ll diff = psum[j]-psum[j-i];
                mmx = max(mmx,diff);
                mmn = min(mmn,diff);
            }
            ans = max(ans, mmx-mmn);
        }
    }
    cout<<ans<<endl;
}

int32_t main()
{
    fastIO;
//  cout.precision(10);
//  cout.setf(ios::fixed);
    psum[0] = 0;
    int t;
    cin >> t;
    while (t--)
        solve();
}