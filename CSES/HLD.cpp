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

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
using vi = vector<int>;
vector<vi>t,parents;
vector<int>level,value,subtree_size, heavy_child, head, id,st;
int mx;

void build(int &n) {
  for (int i = n - 1; i > 0; --i) st[i] = max(st[i<<1] , st[i<<1|1]);
}

void update(int p, int value, int &n) {
  for (st[p += n] = value; p > 1; p >>= 1) st[p>>1] = max(st[p] , st[p^1]);
}

int query(int l, int r, int &n) {
  int res = INT_MIN;
  for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
    if (l&1) res = max(res, st[l++]);
    if (r&1) res = max(res, st[--r]);
  }
  debug(res)
  return res;
}

int dfs(int node, int parent, int cLevel){
    int max_weight = 0;
    level[node] = cLevel;
    parents[0][node] = parent;
    for(auto &child: t[node]){
        if(child!=parent){
            dfs(child,node, cLevel+1);
            subtree_size[node]+=subtree_size[child];
            if(subtree_size[child]>max_weight){
                max_weight = subtree_size[child];
                heavy_child[node] = child;
            }
        }
    }
    return subtree_size[node];
}

void dfs_complete(int node, int parent, int &curr_id,int &n){
    id[node] = curr_id++;
    st[curr_id+n-1] = value[node];
    if(head[node]==-1){
        head[node] = node;
    }
    if(heavy_child[node]!=-1){
        head[heavy_child[node]] = head[node];
        dfs_complete(heavy_child[node],node, curr_id,n);
    }
    for(auto &child: t[node]){
        if(child!=parent and child!=heavy_child[node]) dfs_complete(child, node, curr_id,n);
    }
}

int kthParent(int a, int k){
    for(int i = 0; i<mx; i++){
        if(a==-1) return a;
        if(k&(1<<i)) a = parents[i][a];
    }
    return a;
}

int lca(int a, int b){
    if(level[a]>level[b]){
        a = kthParent(a, level[a] - level[b]);
    }else{
        b = kthParent(b, level[b] - level[a]);
    }
    if(a==b) return a;
    for(int i = mx-1; i>=0; i--){
        if(parents[i][a]!=parents[i][b]){
            a = parents[i][a];
            b = parents[i][b];
        }
    }
    return parents[0][a];
}

int path_ans(int &a, int &b, int &n){
    int LCA = lca(a,b),ans = INT_MIN;
    while(true){
        int curr_head = head[a];
        if(curr_head==head[LCA]){
            ans = max(ans, query(id[LCA],id[a]+1,n));
            break;
        }else{
            ans = max(ans,query(id[curr_head],id[a]+1,n));
        }
        a = parents[0][curr_head];
    }
    while(true){
        int curr_head = head[b];
        if(curr_head==head[LCA]){
            debug(id[LCA]) debug(id[b]+1)
            ans = max(ans, query(id[LCA],id[b]+1,n));
            debug(ans)
            break;
        }else{
            ans = max(ans,query(id[curr_head],id[b]+1,n));
        }
        b = parents[0][curr_head];
    }
    return ans;
}

void initialize(int n){
    t.resize(n+1);
    parents.assign(mx,vi(n+1,-1));
    subtree_size.resize(n+1,1);
    id.resize(n+1);
    heavy_child.assign(n+1,-1);
    head.assign(n+1,-1);
    st.resize(2*n);
    level.resize(n+1);
    value.resize(n+1);
}

void solve()
{
    int n,q;
    cin>>n>>q;
    mx = log2(n) + 2;
    initialize(n);
    for(int i = 1; i<=n; i++) cin>>value[i];
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    dfs(1,-1,0);
    int curr_id = 0;
    dfs_complete(1,-1,curr_id,n);
    build(n);
    for(int i = 1; i<mx; i++){
        for(int j = 1; j<=n; j++){
            int prevParent = parents[i-1][j];
            if(prevParent!=-1)  parents[i][j] = parents[i-1][prevParent];
        }
    }
    while(q--){
        int t,a,b;
        cin>>t>>a>>b;
        if(t==1){
            update(id[a],b,n);
        }else{
            debug(st)
            cout<<path_ans(a,b,n)<<" ";
        }
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}