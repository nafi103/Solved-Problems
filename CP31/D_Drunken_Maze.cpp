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

int n,m;
int x[] = {1,-1,0,0};
int y[] = {0,0,1,-1};

bool valid(int r, int c, int &n, int &m,vector<vector<char>>&grid){
    return r>=0 and r<n and c>=0 and c<=m and grid[r][c]!='#';
}


void solve()
{
    int ans = inf,sr,sc,tr,tc;
    cin>>n>>m;
    vector<vector<char>>grid(n,vector<char>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
            if(grid[i][j]=='S'){
                sr = i;
                sc = j;
            }else if(grid[i][j]=='T'){
                tr = i;
                tc = j;
            }
        }
    }
    bool visited[n][m][4][3];
    memset(visited,0,sizeof(visited));
    using arr = array<int,5>;
    priority_queue<arr,vector<arr>,greater<arr>>q;
    q.push({0,sr,sc,-1,-1});
    while(!q.empty()){
        auto [dis,r,c,d,step] = q.top();
        q.pop();
        if(r==tr and c==tc){
            ans = dis;
            break;
        }
        for(int i = 0; i<4; i++){
            int nr = r+x[i], nc = c+y[i];
            if(valid(nr,nc,n,m,grid)){
                int nstep;
                if(i==d) nstep = step+1;
                else nstep = 0;
                if(nstep>2 or visited[nr][nc][i][nstep]) continue;
                visited[nr][nc][i][nstep] = true;
                q.push({dis+1,nr,nc,i,nstep});
            }
        }
    }
    cout<<(ans!=inf? ans: -1)<<endl;
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