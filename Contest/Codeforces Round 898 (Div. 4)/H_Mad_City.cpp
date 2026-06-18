#include <bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/********************************Macros********************************/

#define mod 1000000007
#define pb push_back
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
#define safe_map unordered_map <long long, long long, custom_hash>
#define safe_hash_table gp_hash_table <long long, long long, custom_hash>

/****************************************************************/

typedef long double ld;
typedef unsigned int ui;
typedef unsigned long long ull;
typedef long double lld;
typedef vector<int> vi;
typedef vector<long long> vll;
typedef vector<pair<int,int>> vpi;
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

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

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

/**********************Functions*********************************/
struct custom_hash {static uint64_t splitmix64(uint64_t x) {x += 0x9e3779b97f4a7c15;x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;x = (x ^ (x >> 27)) * 0x94d049bb133111eb;return x ^ (x >> 31);}
size_t operator()(uint64_t x) const {static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();return splitmix64(x + FIXED_RANDOM);}};
int gcd(int a, int b) {if (b > a) {return gcd(b, a);} if (b == 0) {return a;} return gcd(b, a % b);}
int lcm(int a, int b){return (a/gcd(a,b))*b;}
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
void extendgcd(int a, int b, int*v) {if (b == 0) {v[0] = 1; v[1] = 0; v[2] = a; return ;} extendgcd(b, a % b, v); int x = v[1]; v[1] = v[0] - v[1] * (a / b); v[0] = x; return;} //pass an arry of size1 3
int mminv(int a, int b) {int arr[3]; extendgcd(a, b, arr); return arr[0];} //for non prime b
int mminvprime(int a, int b) {return expo(a, b - 2, b);}
bool revsort(int a, int b) {return a > b;}
int combination(int n, int r, int m, int *fact, int *ifact) {int val1 = fact[n]; int val2 = ifact[n - r]; int val3 = ifact[r]; return (((val1 * val2) % m) * val3) % m;}
void google(int t) {cout << "Case #" << t << ": ";}
vector<int> sieve(int n) {int*arr = new int[n + 1](); vector<int> vect; for (int i = 2; i <= n; i++)if (arr[i] == 0) {vect.push_back(i); for (int j = 2 * i; j <= n; j += i)arr[j] = 1;} return vect;}
int mod_add(int a, int b, int m) {a = a % m; b = b % m; return (((a + b) % m) + m) % m;}
int mod_mul(int a, int b, int m) {a = a % m; b = b % m; return (((a * b) % m) + m) % m;}
int mod_sub(int a, int b, int m) {a = a % m; b = b % m; return (((a - b) % m) + m) % m;}
int mod_div(int a, int b, int m) {a = a % m; b = b % m; return (mod_mul(a, mminvprime(b, m), m) + m) % m;}  //only for prime m
int phin(int n){ int val = 1; for(int i = 2; i*i<=n; i++){ while(n%i==0){val*=(i-1);n/=i; } }if(n>1) val*=(n-1); return val; } //O(sqrt(N))
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 

/****************************************************************/
struct Graph{
    int n;
    vector<vi>v;
    set<int>cycle;
    Graph(int N){
        v.resize(N+1);
        n = N;
    }
    void addEdge(int U, int V){
        v[U].pb(V);
        v[V].pb(U);
    }
    void makeCycle(int s, int d, vi &parent){
        while(s!=d){
            cycle.insert(s);
            s = parent[s];
        }
        cycle.insert(d);
    }
    void bfs(int mar, int val){
        int dest,valTime = INT_MAX,marTime = INT_MAX;
        vector<bool>marVisited(n+1,false),valVis(n+1,false);
        vi marCnt(n+1,INT_MAX),valCnt(n+1,INT_MAX);
        valCnt[val] = 0;
        marCnt[mar] = 0;
        queue<int> q;
        q.push(val);
        while(!q.empty()){
            int x = q.front();
            if(binary_search(all(cycle),x)){
                dest = x;
                valTime = valCnt[x];
                break;
            }
            q.pop();
            if(valVis[x]) continue;
            valVis[x] = true;
            for(auto xx: v[x]){
                if(!valVis[xx]){
                    valCnt[xx] = min(valCnt[xx],valCnt[x]+1);
                    q.push(xx);
                }
            }
        }
        queue<int>qq;
        qq.push(mar);
        while(!qq.empty()){
            int x = qq.front();
            if(x==dest){
                marTime = min(marTime,marCnt[x]);
                break;
            }
            qq.pop();
            if(marVisited[x]) continue;
            marVisited[x] = true;
            for(auto xx: v[x]){
                if(!marVisited[xx]){
                    marCnt[xx] = min(marCnt[xx],marCnt[x]+1);
                    qq.push(xx);
                }
            }
        }
        debug(dest) debug(valTime) debug(marTime)
        if(valTime<marTime) yes;
        else no;
    }
    void dfs(int node, vector<bool>&visited, vi &parent){
        if(visited[node]) return;
        visited[node] = true;
        for(auto x: v[node]){
            if(!visited[x]){
                parent[x] = node;
                dfs(x, visited, parent);
            }else{
                if(x==parent[node]) continue;
                else if(!(binary_search(all(cycle),node))) makeCycle(node,x,parent);
            }
        }
    }
    void checkCycle(){
        vi parent(n+1);
        vector<bool>visited(n+1,false);
        parent[1] = 1;
        dfs(1,visited,parent);
    }
};

void solve()
{
    int n,mar,val;
    cin>>n>>mar>>val;
    Graph g(n);
    rep(i,0,n){
        int u,v;
        cin>>u>>v;
        g.addEdge(u,v);
    }
    g.checkCycle();
    g.bfs(mar,val);
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