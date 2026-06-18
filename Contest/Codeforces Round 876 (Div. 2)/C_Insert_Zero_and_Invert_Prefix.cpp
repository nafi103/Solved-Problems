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
    int n,x;
    cin>>n;
    vector<bool>v(n);
    vi ans;
    rep(i,0,n) {
        cin>>x;
        if(x)   v[i]=1;
        else v[i]=0;
    }
    if(v[n-1]){
        no;
        return;
    }
    int j = 0;
    rev(i,n-1,0) {
        debug(i)
        debug(ans)
        int j = i-1;
        if(!v[i]&&(j<0||!v[j])){
            ans.pb(0);
            continue;
        }
        debug(j)
        while(j>0&&v[j-1]){
            j--;
        }
        debug(j)
        int temp = i - j;
        debug(temp)
        while(temp--)   ans.pb(0);
        ans.pb(i-j);
        i = j;
        debug(i)
    }
    yes;
    writev(ans);
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}