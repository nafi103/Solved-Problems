#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, H, M, diff, hr, minutes;
    cin >> n >> H >> M;
    int vtime = H * 60 + M;
    vector<int> v;
    while (n--)
    {
        int a, b,x;
        cin >> a >> b;
        if((a * 60)+ b < vtime){
            x = 1440 + (a*60)+ b;
        }
        else{
            x = (a * 60)+ b;
        }
        v.push_back(x);
    }
    sort(v.begin(), v.end());
    int mini = v[0];
    if (vtime <= mini)
    {
        diff = mini - vtime;
    }
    else
    {
        diff = 1440 - vtime + mini;
    }
    hr = diff / 60;
    minutes = diff - (hr * 60);
    cout << hr << " " << minutes << endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}