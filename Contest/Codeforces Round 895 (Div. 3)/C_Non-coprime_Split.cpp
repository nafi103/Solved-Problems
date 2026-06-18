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
const int N = 10000007;
vector<int>primes;
vector<bool>mark(N,false);
 void sieve(){
    for(int i = 2; i*i<=N; i++){
        if(!mark[i]){
            for(int j = i*i; j<=N; j+=i){
                mark[j]= true;
            }
        }
    }
    int k = ceil(sqrt(N))+100;
    rep(i,2,k){
        if(!mark[i]) primes.pb(i);
    }
}
 pair<int,int> divisors(int n){
    pair<int,int>d;
    for(int i = 0; primes[i]*primes[i]<=n;i++){
        if(n%primes[i]==0){
            d = {primes[i], n-primes[i]};
            break;
        }
    }
    return d;
}
 void solve()
{
    int l,r;
    cin>>l>>r;
    if(r<=3||(l==r&&!mark[r])){
        cout<<-1<<endl;
        return;
    }
    if(!mark[r]) r--;
    pair<int,int>ans = divisors(r);
    cout<<ans.first<<" "<<ans.second<<endl;
}
 int32_t main()
{
    fastIO;
//  cout.precision(10);
//  cout.setf(ios::fixed);
    sieve();
    int t;
    cin >> t;
    while (t--)
        solve();
}