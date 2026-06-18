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
 void solve()
{
    ll n,ans = 0;
    cin>>n;
    vector<vector<int>>v(n);
    rep(i,0,n){
        int x, k, mn = INT_MAX, mn2 = INT_MAX;
        cin>>x;
        rep(j,0,x){
            cin>>k;
            if(k<mn){
                mn2 = mn;
                mn = k;
            }else if(k<mn2){
                mn2 = k;
            }
        }
        v[i].pb(mn);
        if(x>1)v[i].pb(mn2);
        debug(v[i])
    }
    int k, idx = -1, mn = INT_MAX, mn2 = INT_MAX;
    for(int i = 0; i<n; i++){
        k = (v[i].size()==1)? v[i][0]: v[i][1];
        debug(k)
        if(k<mn){
            mn = k;
            idx = i;
        }
        if(v[i][0]<mn2) mn2 = v[i][0];
        ans+=k;
    }
    if(v[idx].size()==1){
        cout<<ans<<endl;
        return;
    }
    ans-=v[idx][1];
    ans+=mn2;
    cout<<ans<<endl;
}
 int main()
{
    fastIO;
//  cout.precision(10);
//  cout.setf(ios::fixed);
    int t;
    cin >> t;
    while (t--)
        solve();
}