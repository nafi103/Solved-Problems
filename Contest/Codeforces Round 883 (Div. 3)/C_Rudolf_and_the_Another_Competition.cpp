#include <bits/stdc++.h>
using namespace std;
 /********************************Macros********************************/
 #define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
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
    ll n, m, h, x, pen = 0, j = 0, sp = 0,p = 0, s = 0,ans = 1;
    cin>>n>>m>>h;
    vector<ll>v(m);
    rep(i,0,n){
        rep(k, 0, m)
        {
            cin >> v[k];
        }
        sort(all(v));
        for(int k = 1; k <m;k++){
            v[k]+=v[k-1];
            if(v[k-1]<=h){
                s++;
                p += v[k - 1];
            }
        }
        if(v[m-1]<=h){
            p+=v[m-1];
            s++;
        }
        if(i==0){
            pen = p, sp = s;
            p = 0, s = 0, j = 0;
            continue;
        }else{
            if (s > sp || (s == sp && p < pen))
                ans++;
        }
        p = 0,s = 0, j = 0;
    }
    cout<<ans<<"\n";
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}