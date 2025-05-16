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
const int inf = 1e18+10;
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
int dx[] = {-2, -2, -1, -1, 1, 1, 2, 2};
int dy[] = {-1, 1, -2, 2, -2, 2, -1, 1};

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<m;
}

void solve()
{
    int cnt = 0;
    cin>>n>>m;
    vector<vector<char>>grid(n,vector<char>(m));
    for(auto &x: grid){
        for(auto &y: x){
            cin>>y;
            if(y!='.')
                cnt++;
        }
    }
    if(cnt==0){
        cout<<0<<endl;
        return;
    }
    if(n==1 or m==1){
        cout<<-1<<endl;
        return;
    }
    vector<vector<int>>final_distance(n,vector<int>(m,0));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            if(grid[i][j]=='.')
                continue;
            int move = grid[i][j] - '0';
            vector<vector<int>>distance(n,vector<int>(m,inf));
            using arr = array<int,3>;
            priority_queue<arr,vector<arr>,greater<arr>> pq;
            distance[i][j] = 0;
            pq.push({0,i,j});
            while(!pq.empty()){
                auto [d,r,c] = pq.top();
                pq.pop();
                for(int k = 0; k<8; k++){
                    int nr = r+dx[k], nc = c+dy[k];
                    if(valid(nr,nc) and distance[nr][nc]>d+1){
                        distance[nr][nc] = d+1;
                        pq.push({d+1,nr,nc});
                    }
                }
            }
            for(int k = 0; k<n; k++){
                for(int l = 0; l<m; l++){
                    if(distance[k][l]!=inf){
                        distance[k][l] = (distance[k][l]+move-1)/move;
                    }
                }
            }
            for(int k = 0; k<n; k++){
                for(int l = 0; l<m; l++){
                    final_distance[k][l] = min(inf,distance[k][l]+final_distance[k][l]);
                }
            }
        }
    }
    int ans = inf;
    for(auto &x: final_distance){
        for(auto &y: x){
            ans = min(ans,y);
        }
    }
    cout<<(ans==inf? -1: ans)<<endl;
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