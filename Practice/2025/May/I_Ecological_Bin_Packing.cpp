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

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    map<char,int>mp = {
        {'B',0},{'G',1},{'C',2}
    };
    int n = 9;
    vector<int>v(n);
    while(cin>>v[0]){
        for(int i = 1; i<n; i++){
            cin>>v[i];
        }
        string curr = "BCG", ans = curr;
        int mn = INT_MAX;
        do{
            int op = v[mp[curr[0]]+3] + v[mp[curr[0]]+6];
            op+=v[mp[curr[1]]] + v[mp[curr[1]]+6];
            op+=v[mp[curr[2]]] + v[mp[curr[2]]+3];
            if(op<mn){
                mn = op;
                ans = curr;
            }
        }while(next_permutation(all(curr)));
        cout<<ans<<" "<<mn<<endl;
    }
}