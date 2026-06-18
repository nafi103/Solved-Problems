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
using vc = vector<char>;
using vb = vector<bool>;
const int n = 8;
vector<vc>grid(n,vector<char>(n));

int x[] = {1,1,1,-1,-1,-1,0,0};
int y[] = {0,1,-1,1,-1,0,1,-1};

void mark(int i, int j, vector<vb>&visited){
    for(int p = 0; p<8; p++){
        int ti = i+x[p], tj = j+y[p];
        while(ti>=0 and ti<n and tj>=0 and tj<n){
            visited[ti][tj] = true;
            ti+=x[p];
            tj+=y[p];
        }
    }
}

int f(int i, int j, int queens, vector<vb>visited){
    if(queens==0) return 1;
    if(i==n) return 0;
    if(8-queens!=i) return 0;
    if(visited[i][j] or grid[i][j]=='*') return f(i+(j==n-1), (j+1)%n, queens, visited);
    int ans = 0;
    ans+=f(i+(j==n-1), (j+1)%n, queens, visited);
    visited[i][j] = true;
    queens--;
    mark(i,j,visited);
    ans+=f(++i, 0, queens, visited);
    return ans;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cin>>grid[i][j];
        }
    }
    vector<vb>visited(n,vb(n,false));
    int ans = f(0,0,8,visited);
    cout<<ans<<endl;
}