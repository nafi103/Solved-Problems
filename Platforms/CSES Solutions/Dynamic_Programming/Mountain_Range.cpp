#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

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

void solve()
{
    int n;
    cin>>n;
    vector<int>v(n),in_degree(n,0);
    readv(v);
    vector<vector<int>>g(n);
    stack<int>left_st, right_st;
    for(int i = 0; i<n; i++){
        while(!left_st.empty() and v[left_st.top()]<v[i]){
            int pos = left_st.top();
            g[i].push_back(pos);
            in_degree[pos]++;
            left_st.pop();
        }
        left_st.push(i);
        int j = n-1-i;
        while(!right_st.empty() and v[right_st.top()]<v[j]){
            int pos = right_st.top();
            g[j].push_back(pos);
            in_degree[pos]++;
            right_st.pop();
        }
        right_st.push(j);
    }
    vector<int>ans(n,1);
    queue<int>q;
    for(int i = 0; i<n; i++)
        if(in_degree[i]==0)
            q.push(i);
    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(auto &child: g[node]){
            if(ans[child]<=ans[node]){
                ans[child] = ans[node]+1;
            }
            in_degree[child]--;
                if(in_degree[child]==0)
                    q.push(child);
        }
    }
    cout<<*max_element(all(ans))<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}