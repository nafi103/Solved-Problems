#include<bits/stdc++.h>
#define int long long
using namespace std;
#define all(x) x.begin(), x.end()
const int MAX = 5e6 + 6;
const int inf = 1e10;

pair<int,int> calc_slope(int y, int x){
    if(y==0){
        return {0,0};
    }
    if(x==0){
        return {inf,inf};
    }
    int g = gcd(y,x);
    if (g != 0) {
        y/=g;
        x/=g;
    }
    if(y<0){
        y*=-1;
        x*=-1;
    }
    return {y,x};
}

int32_t main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL), cout.tie(NULL);
    int n,m;
    cin>>n>>m;
    vector<pair<int,int>>demon(m);
    for(auto &[f,s]: demon){
        cin>>f>>s;
    }
    vector<int>ans(n+1,1);
    for(int i = 0; i<m;  i++){
        int add = 0;
        map<pair<int,int>, int>slope;
        for(int j = 0; j<m; j++){
            if(i==j)
                continue;
            if(demon[i]==demon[j]){
                add++;
                continue;
            }
            slope[calc_slope(demon[j].second-demon[i].second,demon[j].first-demon[i].first)]++;
        }
        for(auto &[slp,cnt]: slope){
            if(slp==make_pair(0ll,0ll) or !slp.first){
                continue;
            }
            if(slp==make_pair(inf,inf) and demon[i].first>=1 and demon[i].first<=n){
                ans[demon[i].first] = max(ans[demon[i].first],cnt+1);
            }else{
                int my_y = demon[i].second, slope_y = slp.first;
                if(slope_y != 0 and my_y % slope_y==0){
                    int laser_x = demon[i].first - (my_y/slope_y)*slp.second;
                    if(laser_x>=1 and laser_x<=n){
                        ans[laser_x] = max(ans[laser_x],cnt+add+1);
                    }
                }
            }
        }
    }
    for(int i = 1; i<=n; i++){
        cout<<ans[i]<<" ";
    }
    return 0;
}