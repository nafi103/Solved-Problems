#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

class ele
{
    public:
    int u, v, wt;
};
class check
{
    public:
    bool operator()(ele a, ele b)
    {
        return a.wt > b.wt;
    }
};
struct Graph{
    vector<vector<pair<int,int>>>v;
    int n;
    Graph(int N){
        v.resize(N);
        n = N;
    }
    void add(int uu, int vv, int wt){
        v[uu].pb({vv,wt});
        v[vv].pb({uu,wt});
    }
    int makeMST(int start){
        int cost = 0;
        priority_queue<ele, vector<ele>, check> pq;
        vector<bool>visited(n,false);
        for (auto x : v[start])
        {
            pq.push({start,x.first,x.second});
        };
        visited[start] = true;
        while(!pq.empty()){
            auto z = pq.top();
            pq.pop();
            if(visited[z.v]) continue;
            else{
                visited[z.v] = true;
                cost+=z.wt;
                for(auto x: v[z.v]){
                    pq.push({z.v,x.first,x.second});
                }
            }
        }
        for(int i = 0; i<n; i++){
            if(!visited[i])
                return -1;
        }
        return cost;
    }
};


void solve()
{
    map<string,int>mp;
    int n;
    cin>>n;
    vector<array<int,3>>tmp;
    tmp.reserve(n);
    while(n--){
        string a,b;
        int c;
        cin>>a>>b>>c;
        int ia = (mp.count(a)?mp[a]:mp[a]=sz(mp));
        int ib = (mp.count(b)?mp[b]:mp[b]=sz(mp));
        tmp.push_back({ia,ib,c});
    }
    Graph g(sz(mp));
    for(auto &[u,v,w]: tmp){
        g.add(u,v,w);
    }
    int ans = g.makeMST(0);
    if(ans==-1){
        cout<<"Impossible"<<endl;
    }else{
        cout<<ans<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}