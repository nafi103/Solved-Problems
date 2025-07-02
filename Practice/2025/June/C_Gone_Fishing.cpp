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

int n;
vector<int>fish,rate,road,spent_time;
vector<vector<int>>dp;

int f(int pos, int time){
    int &ans = dp[pos][time],get_fish = 0, curr_fish = fish[pos];
    if(ans!=-1)
        return ans;
    if(pos==n-1){
        while(time--){
            if(curr_fish<=0)
                break;
            get_fish+=curr_fish;
            curr_fish-=rate[pos];
        }
        return ans = get_fish;
    }
    ans = 0;
    if(road[pos]<=time)
        ans = f(pos+1,time-road[pos]);
    while(time--){
        get_fish+=curr_fish;
        curr_fish-=min(curr_fish,rate[pos]);
        if(road[pos]<=time)
            ans = max(ans, get_fish + f(pos+1,time-road[pos]));
        else
            ans = max(ans, get_fish);
    }
    return ans;
}

void solve()
{
    fish.clear();
    rate.clear();
    road.clear();
    dp.clear();
    int time;
    cin>>n>>time;
    time = time*12;
    fish.resize(n);
    rate.resize(n);
    road.resize(n-1);
    spent_time.assign(n,0);
    readv(fish);
    readv(rate);
    readv(road);
    dp.resize(n,vector<int>(time+1,-1));
    int ans = f(0,time), final_ans = ans;
    for(int i = 0; i<n; i++){
        if(time==0 or i==n-1){
            spent_time[i] = time;
            continue;
        }
        spent_time[i] = time;
        int get_fish = 0, curr_fish = fish[i];
        int new_time = 0, new_ans = 0;
        for(int j = 0; j<=time; j++, get_fish+=curr_fish, curr_fish-=min(curr_fish,rate[i])){
            if(time-j-road[i]>0){
                if(get_fish+dp[i+1][time-j-road[i]]==dp[i][time]){
                    spent_time[i] = j;
                    new_time = time-j-road[i];
                    new_ans = dp[i+1][time-j-road[i]];
                }
            }
        }
        time = new_time;
        ans = new_ans;
    }
    for(int i = 0; i<n; i++){
        cout<<spent_time[i]*5<<"";
        if(i<n-1)
            cout<<", ";
    }
    cout<<endl;
    cout<<"Number of fish expected: "<<final_ans<<endl;
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}