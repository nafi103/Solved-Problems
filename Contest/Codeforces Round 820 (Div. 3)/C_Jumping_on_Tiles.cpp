#include <bits/stdc++.h>
#define frm for (int i = 1; i < str.size(); i++)
using namespace std;
 void solution()
{
    vector<pair<int, int>> v;
    vector<int> v1;
    int cost = 0, steps = 1;
    string str;
    cin >> str;
    int r1 = str[0], r2 = (int)str[str.size() - 1];
    frm
    {
        if ((str[i] >= r1 && str[i] <= r2) || (str[i] <= r1 && str[i] >= r2))
        {
            int x = (int)str[i] - 96;
            v.push_back(make_pair(x, (i + 1)));
        }
    }
    r1 = (int)r1-96;
    r2 = (int)r2-96;
    if (r1 < r2)
        sort(v.begin(), v.end());
    else
        sort(v.rbegin(), v.rend());
    /*for (int i = 0; i < v.size(); i++)
    {
        cout<<v[i].first<<" "<<v[i].second<<endl;
    }*/
    cost += abs(v[0].first - r1);
    steps++;
    for (int i = 1; i < v.size(); i++)
    {
        cost += abs(v[i].first - v[i - 1].first);
        steps++;
    }
    cout << cost << " " << steps << endl;
    cout<<"1 ";
    for (int i = 0; i < v.size(); i++)
    {
        if(v[i].second==str.size()) continue;
        cout<<v[i].second<<" ";
    }
    cout<<str.size()<<endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}