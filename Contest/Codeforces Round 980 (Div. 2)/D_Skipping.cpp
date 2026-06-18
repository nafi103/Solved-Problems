#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
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
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

int read(){
    int x=0,f=1;char ch=getchar();while(ch<'0'||ch>'9'){if(ch=='-')f=-1;ch=getchar();}
    while(ch>='0'&&ch<='9'){x=(x<<1)+(x<<3)+(ch^48);ch=getchar();}return x*f;
}

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
using vi = vector<int>;
using vpi = vector<pair<int,int>>;
using pii = pair<int,int>;

struct Graph{
    vector<vpi>v;
    int n;
    Graph(int N){
        v.resize(N+1);
        n = N;
    }
    void add(int uu, int vv, int wt){
        v[uu].pb({vv,wt});
    }
    vector<int> dijsktra(int src)
    {
        priority_queue<pii, vector<pii>, greater<pii>> pq;
        vi distance(n+1, inf);
        distance[src] = 0;
        pq.push({0, src});
        while (!pq.empty())
        {
            pii p = pq.top();
            pq.pop();
            if(p.ff>distance[p.ss])    continue;
            for (auto &[nbr,wt] : v[p.second])
            {
                if (distance[nbr] > distance[p.second] + wt)
                {
                    distance[nbr] = distance[p.second] + wt;
                    pq.push({distance[nbr], nbr});
                }
            }
        }
        return distance;
    }
};
 
void solve()
{
    int n = read();
    Graph g(n);
    vi a(n),b(n);
    for(auto &x: a) x = read();
    for(auto &x: b) x = read();
    for(int i = 0; i<n; i++){
        if(b[i]>i+1){
            g.add(i+1,b[i],a[i]);
        }
        if(i) g.add(i+1,i,0);
    }
    int ans = a[0];
    vi dist = g.dijsktra(1);
    for(int i = 1; i<n; i++) a[i]+=a[i-1];
    for(int i = 2; i<=n; i++){
        ans = max(ans, a[i-1] - dist[i]);
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    t = read();
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}