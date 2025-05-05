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

bool valid(int i, int j, int k, int l, int m, int n){
    return abs(k-i)+abs(l-j)>0 and abs(m-k)+abs(n-l)>0 and abs(m-i)+abs(n-j)>0 
    and abs(k-i)<2 and abs(l-j)<2 and abs(m-k)<2 and abs(n-l)<2;
}

void solve()
{
    string ans = "CCC";
    vector<string>grid(3);
    for(int i = 0; i<3; i++){
        cin>>grid[i];
    }
    for(int i = 0; i<3; i++){
        for(int j = 0; j<3; j++){
            for(int k = 0; k<3; k++){
                for(int l = 0; l<3; l++){
                    for(int m = 0; m<3; m++){
                        for(int n = 0; n<3; n++){
                            if(valid(i,j,k,l,m,n)){
                                string curr = "";
                                curr.pb(grid[i][j]);
                                curr.pb(grid[k][l]);
                                curr.pb(grid[m][n]);
                                ans = min(ans,curr);
                            }
                        }
                    }
                }
            }
        }
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}